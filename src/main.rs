// ------
// Variables and literals
// ------

#[derive(Copy, Clone)]
struct Var(i32);
const VAR_UNDEF: Var = Var(-1);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(i32);

impl Lit {
    fn new(Var(var): Var, sign: bool) -> Lit {
        Lit(2 * var + sign as i32)
    }

    pub fn sign(&self) -> bool {
        ((self.0) & 1) != 0
    }
}

pub const LIT_UNDEF: Lit = Lit(-2);
pub const LIT_ERROR: Lit = Lit(-1);

#[repr(u8)]
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum LBool {
    True,
    False,
    Undef,
}

impl Default for LBool {
    fn default() -> Self {
        LBool::Undef
    }
}

// TODO &&, ||

pub struct Clause {
    mark: u8,
    learnt: bool,
    has_extra: bool,
    reloced: bool,
    size: usize,
}

type ClauseRef = usize; // TODO

type VMap<T> = Vec<T>;
type LSet = Vec<u8>; // ???

#[derive(Default, Copy, Clone)]
struct VariableData {
    reason: Option<ClauseRef>,
    level: i32,
}

struct ShrinkStackElem {
    i: u32,
    l: Lit,
}

// derive copy?
#[derive(Clone, PartialEq, Eq)]
struct Watcher {
    cref: u32,
    blocker: Lit,
}

struct OrderHeap {
    heap: Vec<Var>,
    indices: VMap<i32>,
}

impl OrderHeap {
    pub fn left(i: i32) -> i32 {
        i * 2 + 1
    }
    pub fn right(i: i32) -> i32 {
        (i + 1) * 2
    }
    pub fn parent(i: i32) -> i32 {
        (i - 1) >> 1
    }

    pub fn percolate_up(&mut self, mut i: i32, act: &[f64]) {
        let var = self.heap[i as usize];

        let mut p = Self::parent(i);
        while i != 0 && act[var.0 as usize] < act[self.heap[p as usize].0 as usize] {
            self.heap[i as usize] = self.heap[p as usize];
            self.indices[self.heap[p as usize].0 as usize] = i;
            i = p;
            p = Self::parent(p);
        }

        self.heap[i as usize] = var;
        self.indices[var.0 as usize] = i;
    }

    pub fn percolate_down(&mut self, mut i: i32, act: &[f64]) {
        let var = self.heap[i as usize];
        while (Self::left(i) as usize) < self.heap.len() {
            let child = if (Self::right(i) as usize) < self.heap.len()
                && act[self.heap[Self::right(i) as usize].0 as usize]
                    < act[self.heap[Self::left(i) as usize].0 as usize]
            {
                Self::right(i)
            } else {
                Self::left(i)
            };

            if !(act[self.heap[child as usize].0 as usize] < act[var.0 as usize]) {
                break;
            }

            self.heap[i as usize] = self.heap[child as usize];
            self.indices[self.heap[i as usize].0 as usize] = i;
            i = child;
        }

        self.heap[i as usize] = var;
        self.indices[var.0 as usize] = i;
    }

    pub fn contains(&self, Var(var) :Var) -> bool { (var as usize) < self.indices.len() && self.indices[var as usize] == 1 }

    pub fn decreased(&mut self, key :Var, act :&[f64]) {
        debug_assert!(self.contains(key));
        self.percolate_up(self.indices[key.0 as usize], act);
    }

    pub fn increased(&mut self, key :Var, act :&[f64]) {
        debug_assert!(self.contains(key));
        self.percolate_down(self.indices[key.0 as usize], act);
    }

    pub fn update(&mut self, key :Var, act :&[f64]) {
        if !self.contains(key) { self.insert(key, act); }
        else { 
            self.percolate_up(self.indices[key.0 as usize], act);
            self.percolate_down(self.indices[key.0 as usize], act);
        }
    }

    pub fn insert(&mut self, key :Var, act :&[f64]) {
        self.indices.resize(key.0 as usize, -1);
        debug_assert!(!self.contains(key));

        self.indices[key.0 as usize] = self.heap.len() as i32;
        self.heap.push(key);
        self.percolate_up(self.indices[key.0 as usize], act);
    }

    pub fn remove(&mut self, key :Var, act :&[f64]) {
        debug_assert!(self.contains(key));
        let k_pos = self.indices[key.0 as usize];
        self.indices[key.0 as usize] = -1;

        if k_pos < self.heap.len() as i32 - 1 {
            self.heap[k_pos as usize] = self.heap[self.heap.len()-1];
            self.indices[self.heap[k_pos as usize].0 as usize] = k_pos;
            self.heap.pop();
            self.percolate_down(k_pos, act);
        } else {
            self.heap.pop();
        }
    }

    pub fn remove_min(&mut self, act :&[f64]) -> Var {
        let var = self.heap[0];
        self.heap[0] = self.heap[self.heap.len()-1];
        self.indices[self.heap[0].0 as usize] = 0;
        self.indices[var.0 as usize] = -1;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.percolate_down(0, act);
        }
        var
    }
}

pub struct Solver {
    pub verbosity: u32,
    // Extra results (read-only for consumer)
    pub model: Vec<LBool>,
    pub conflict: LSet,

    pub params: SolverParams,
    pub stats: SolverStatistics,

    // solver state
    clauses: Vec<ClauseRef>,
    learnts: Vec<ClauseRef>,
    trail: Vec<Lit>,
    trail_lim: Vec<i32>,
    assumptions: Vec<Lit>,

    // variable maps
    activity: VMap<f64>, // indexed by variable (>0)
    assigns: VMap<LBool>,
    polarity: VMap<i8>,
    user_pol: VMap<LBool>,
    decision: VMap<i8>,
    vardata: VMap<VariableData>,

    watch_occs: VMap<Vec<Watcher>>,
    watch_dirty: VMap<i8>,
    watch_dirties: Vec<Lit>,

    order_heap: OrderHeap,

    ok: bool,
    cla_inc: f64,
    var_inc: f64,
    qhead: usize,
    simp_db_assigns: i32,
    simp_db_props: usize,
    progress_estimate: f64,
    remove_satisfied: bool,
    next_var: i32,
    clause_arena: (), // TODO

    released_vars: Vec<Var>,
    free_vars: Vec<Var>,
    seen: VMap<i8>,
    analyze_stack: Vec<ShrinkStackElem>, // TODO
    analyze_toclear: Vec<Lit>,
    add_tmp: Vec<Lit>,

    max_learnts: f64,
    learntsize_adjust_confl: f64,
    learntsize_adjust_cnt: i32,

    conflict_budget: i64,
    propagation_budget: i64,
    asynch_interrupt: bool,
}

pub struct SolverParams {
    var_decay: f64,
    clause_decay: f64,
    random_var_freq: f64,
    random_seed: f64,
    luby_restart: bool,
    ccmin_mode: i32,
    phase_saving: i32,
    rnd_pol: bool,
    rnd_init_act: bool,
    garbage_frac: f64,
    min_learnts_lim: u32,
    restart_first: u32,
    restart_inc: f64,
    learntsize_factor: f64,
    learntsize_inc: f64,
    learntsize_adjust_start_confl: i32,
    learntsize_adjust_inc: f64,
}

impl Default for SolverParams {
    fn default() -> Self {
        SolverParams {
            var_decay: 0.95,
            clause_decay: 0.999,
            random_var_freq: 0.0,
            random_seed: 91648253.0,
            luby_restart: true,
            ccmin_mode: 2,
            phase_saving: 2,
            rnd_pol: false,
            rnd_init_act: false,
            garbage_frac: 0.20,
            min_learnts_lim: 0,
            restart_first: 100,
            restart_inc: 2.0,
            learntsize_factor: 1.0 / 3.0,
            learntsize_inc: 1.1,
            learntsize_adjust_start_confl: 100,
            learntsize_adjust_inc: 1.5,
        }
    }
}

#[derive(Default)]
pub struct SolverStatistics {
    solves: usize,
    starts: usize,
    decisions: usize,
    rnd_decisions: usize,
    propagations: usize,
    conflicts: usize,
    dec_vars: usize,
    num_clauses: usize,
    num_learnts: usize,
    clauses_literals: usize,
    learnts_literals: usize,
    max_literals: usize,
    tot_literals: usize,
}

impl Solver {
    pub fn new() -> Self {
        Solver {
            verbosity: 1,
            watch_occs: Vec::new(),
            watch_dirty: Vec::new(),
            watch_dirties: Vec::new(),

            order_heap: OrderHeap {
                heap: Vec::new(),
                indices: Vec::new(),
            },
            ok: true,
            cla_inc: 1.0,
            var_inc: 1.0,
            qhead: 0,
            simp_db_assigns: -1,
            simp_db_props: 0,
            progress_estimate: 0.0,
            remove_satisfied: true,
            next_var: 0,
            conflict_budget: -1,
            propagation_budget: -1,
            asynch_interrupt: false,
            activity: Vec::new(),
            add_tmp: Vec::new(),
            analyze_stack: Vec::new(),
            analyze_toclear: Vec::new(),
            assigns: Vec::new(),
            assumptions: Vec::new(),
            clause_arena: (), // TODO
            conflict: Vec::new(),
            clauses: Vec::new(),
            decision: Vec::new(),
            free_vars: Vec::new(),
            learnts: Vec::new(),
            learntsize_adjust_cnt: 0,
            learntsize_adjust_confl: 0.0,
            max_learnts: 0.0,
            model: Vec::new(),

            polarity: Vec::new(),
            released_vars: Vec::new(),
            seen: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            user_pol: Vec::new(),
            vardata: Vec::new(),

            // substructs
            params: Default::default(),
            stats: Default::default(),
        }
    }

    pub fn new_var(&mut self, user_polarity: LBool, decision_var: bool) -> Lit {
        let var = if let Some(var) = self.free_vars.pop() {
            var
        } else {
            let idx = self.next_var;
            self.next_var += 1;
            Var(idx)
        };

        map_insert(
            &mut self.watch_occs,
            Lit::new(var, false).0 as usize,
            Default::default(),
            Default::default(),
        );
        map_insert(
            &mut self.watch_occs,
            Lit::new(var, true).0 as usize,
            Default::default(),
            Default::default(),
        );
        map_insert(
            &mut self.watch_dirty,
            Lit::new(var, false).0 as usize,
            Default::default(),
            Default::default(),
        );
        map_insert(
            &mut self.watch_dirty,
            Lit::new(var, true).0 as usize,
            Default::default(),
            Default::default(),
        );

        var_map_insert(
            &mut self.assigns,
            var,
            Default::default(),
            Default::default(),
        );
        var_map_insert(
            &mut self.vardata,
            var,
            Default::default(),
            Default::default(),
        );
        var_map_insert(
            &mut self.activity,
            var,
            if self.params.rnd_init_act {
                drand(&mut self.params.random_seed) * 0.00001
            } else {
                0.0
            },
            0.0,
        );
        var_map_insert(&mut self.seen, var, Default::default(), Default::default());
        var_map_insert(&mut self.polarity, var, 1, 1);
        var_map_insert(&mut self.user_pol, var, user_polarity, Default::default());
        self.decision.resize(var.0 as usize + 1, 1);
        // trail.capacity(v+1) // not needed?

        Lit(var.0) // TODO
    }

    fn set_decision_var(&mut self, var: Var, b: bool) {
        if b && self.decision[var.0 as usize] == 0 {
            self.stats.dec_vars += 1;
        }
        if !b && self.decision[var.0 as usize] != 0 {
            self.stats.dec_vars -= 1;
        }

        self.decision[var.0 as usize] = b as i8;
        self.insert_var_order(var);
    }

    fn insert_var_order(&mut self, var: Var) {
        unimplemented!()
    }
}

fn var_map_insert<T: Default + Clone>(map: &mut Vec<T>, Var(idx): Var, value: T, default: T) {
    map_insert(map, idx as usize, value, default)
}

fn map_insert<T: Default + Clone>(map: &mut Vec<T>, idx: usize, value: T, default: T) {
    map.resize(idx as usize + 1, default);
    map[idx as usize] = value;
}

fn drand(seed: &mut f64) -> f64 {
    let n: f64 = 2147483647.0;
    *seed *= 1389796.0;
    let q = (*seed / n) as i32;
    *seed -= q as f64 * n;
    *seed / n
}

fn irand(seed: &mut f64, size: i32) -> i32 {
    (drand(seed) as i32 * size)
}

fn main() {
    println!("Hello, world!");
}
