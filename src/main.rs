use bitfield::bitfield;

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

    fn sign(&self) -> bool {
        ((self.0) & 1) != 0
    }

    fn var(&self) -> Var {
        Var(self.0 >> 1)
    }

    fn inverse(&self) -> Lit {
        Self::new(self.var(), !self.sign())
    }
}

pub const LIT_UNDEF: Lit = Lit(-2);
pub const LIT_ERROR: Lit = Lit(-1);

#[repr(u8)]
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum LBool {
    False = 0,
    True = 1,
    Undef = 2,
}

impl LBool {
    fn xor(&self, b :bool) -> LBool {
        unsafe { std::mem::transmute((*self as u8) ^ (b as u8)) }
    }
}

impl Default for LBool {
    fn default() -> Self {
        LBool::Undef
    }
}

// TODO &&, ||

bitfield! {
    pub struct ClauseHeader(u32);
    get_mark, set_mark :2, 0;
    get_learnt, set_learnt :1, 3;
    get_extra_data, set_extra_data :1, 4;
    get_reloced, set_reloced :1, 5;
    get_size, set_size :27, 6;
}

type ClauseHeaderOffset = i32;
const CLAUSE_NONE: ClauseHeaderOffset = -1;

type VMap<T> = Vec<T>;
type LSet = Vec<u8>; // ???

#[derive(Default, Copy, Clone)]
struct VariableData {
    reason: ClauseHeaderOffset,
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

    pub fn decrease(&mut self, key :Var, act :&[f64]) {
        debug_assert!(self.contains(key));
        self.percolate_up(self.indices[key.0 as usize], act);
    }

    pub fn increase(&mut self, key :Var, act :&[f64]) {
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

struct ClauseDatabase {
    clause_data: Vec<u32>,
}

impl ClauseDatabase {
    fn add_clause(&mut self, lits :&[Lit], extra_data :bool) -> ClauseHeaderOffset {
        let header_size = std::mem::size_of::<ClauseHeader>();
        let data_size = lits.len();
        
        let mut header = ClauseHeader(0);
        header.set_size(data_size as u32);
        header.set_extra_data(extra_data as u32);
        let header = header;

        let cref = self.clause_data.len() as i32;
        self.clause_data.push(unsafe {
            std::mem::transmute::<ClauseHeader,u32>(header)
        });
        self.clause_data.extend(unsafe {
            std::slice::from_raw_parts(lits.as_ptr() as *const Lit as *const u32, lits.len())
        });

        if extra_data {
            self.clause_data.push(unsafe {
                std::mem::transmute::<f32,u32>(0.0)
            });
        }

        cref
    }

    fn get_activity<'a>(&'a mut self, header_addr :ClauseHeaderOffset) -> &'a mut f32 {
        let header = self.get_header(header_addr);
        unsafe {
            let ptr = (self.clause_data.get_mut(header_addr as usize).unwrap() as *mut u32 as *mut f32)
                .offset((1 + header.get_size()) as isize  *std::mem::size_of::<u32>() as isize);
            &mut *ptr
        }
    }

    fn get_header(&self, header_addr :ClauseHeaderOffset) -> ClauseHeader {
        assert!(header_addr >= 0);
        assert_eq!(std::mem::size_of::<ClauseHeader>(), std::mem::size_of::<u32>());
        let val = self.clause_data[header_addr as usize];
        unsafe {
            std::mem::transmute::<u32,ClauseHeader>(val)
        }
    }

    fn get_lits<'a>(&'a self, header_addr :ClauseHeaderOffset, size :usize) -> &'a [Lit] {
        unsafe {
            let ptr = (&self.clause_data[header_addr as usize] as *const u32 as *const Lit)
                .offset(std::mem::size_of::<ClauseHeader>() as isize);
            std::slice::from_raw_parts(ptr, size)
        }
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
    clause_database :ClauseDatabase,
    clauses: Vec<ClauseHeaderOffset>,
    learnts: Vec<ClauseHeaderOffset>,

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

            clause_database: ClauseDatabase {
                clause_data: Vec::new(),
            },
            clauses: Vec::new(),
            learnts: Vec::new(),

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
            conflict: Vec::new(),
            decision: Vec::new(),
            free_vars: Vec::new(),
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
            Var((self.next_var, self.next_var += 1).0)
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
        if !self.order_heap.contains(var) && self.decision[var.0 as usize] == 1 {
            self.order_heap.insert(var, &self.activity);
        }
    }

    fn var_decay_activity(&mut self) {
        self.var_inc *= (1.0 / self.params.var_decay);
    }

    fn var_bump_activity_default(&mut self, var :Var) {
        self.var_bump_activity(var, self.var_inc);
    }

    fn var_bump_activity(&mut self, var :Var, inc :f64) {
        self.activity[var.0 as usize] += inc;
        if self.activity[var.0 as usize] > 1e100 {
            // rescale
            for act in &mut self.activity {
                *act *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }

        // update heap
        if self.order_heap.contains(var) {
            self.order_heap.decrease(var, &self.activity);
        }
    }

    fn clause_decay_activity(&mut self) {
        self.cla_inc *= (1.0 / self.params.clause_decay);
    }

    fn clause_bump_activity(&mut self, cref :ClauseHeaderOffset) {
        let activity = self.clause_database.get_activity(cref);
        *activity += self.cla_inc as f32;
        if *activity > 1e20 {
            // rescale
            for p in self.learnts.iter() {
                *self.clause_database.get_activity(*p) *= 1e-20;
            }
            self.cla_inc *= 1e-20;
        }
    }

    fn release_var(&mut self, l :Lit) {
        if self.lit_value(l) == LBool::Undef {
            self.add_clause(std::iter::once(l));
            self.released_vars.push(l.var());
        }
    }

    fn var_value(&self, var :Var) -> LBool {
        self.assigns[var.0 as usize]
    }

    fn lit_value(&self, lit :Lit) -> LBool {
        Self::assigns_lit_value(&self.assigns, lit)
    }

    fn assigns_lit_value(assigns :&Vec<LBool>, lit :Lit) -> LBool {
        LBool::xor(&assigns[lit.var().0 as usize], lit.sign())
    }

    fn add_clause(&mut self, ps :impl Iterator<Item = Lit>) -> bool {
        assert!(self.trail_lim.len() == 0);
        if !self.ok { return false; }

        self.add_tmp.clear();
        self.add_tmp.extend(ps);
        self.add_tmp.sort();
        {
            let mut prev = LIT_UNDEF;
            let mut already_sat = false;
            let add_tmp = &mut self.add_tmp;
            let assigns = &self.assigns;
            add_tmp.retain(|l| {
                if Self::assigns_lit_value(assigns, *l) == LBool::False || *l == prev.inverse() {
                    already_sat = true;
                }
                !(   /* dedup */ (prev, prev=*l).0 == *l
                  || /* known */ Self::assigns_lit_value(assigns, *l) == LBool::True)
            });

            if already_sat { return true; }
        }

        if self.add_tmp.len() == 0  {
            self.ok = false;
            return false;
        } else if self.add_tmp.len() == 1 {
            self.unchecked_enqueue(self.add_tmp[0]);
            self.ok = self.propagate() == CLAUSE_NONE;
            return self.ok;
        } else {
            let cref = self.clause_database.add_clause(&self.add_tmp, false);
            self.clauses.push(cref);
            self.attach_clause(cref);
        }

        true
    }

    fn attach_clause(&mut self, cref :ClauseHeaderOffset) {
        let header = self.clause_database.get_header(cref);
        assert!(header.get_size() > 1);
    }


    fn unchecked_enqueue(&mut self, lit :Lit) {
        unimplemented!()
    }

    fn propagate(&mut self) -> ClauseHeaderOffset {
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
