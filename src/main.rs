// ------
// Variables and literals
// ------

#[derive(Copy,Clone)]
struct Var(i32);
const VAR_UNDEF: Var = Var(-1);

#[derive(Copy,Clone)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
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
#[derive(Copy,Clone)]
#[derive(PartialEq, Eq)]
pub enum LBool {
    True,
    False,
    Undef,
}

impl Default for LBool {
    fn default() -> Self { LBool::Undef }
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
    watches: (),    // TODO
    order_heap: (), // TODO

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
    analyse_stack: Vec<()>, // TODO
    analyse_toclear: Vec<Lit>,
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
            watches: (),    // TODO
            order_heap: (), // TODO
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
            analyse_stack: Vec::new(),
            analyse_toclear: Vec::new(),
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


    pub fn new_var(&mut self, user_polarity :LBool, decision_var :bool) -> Lit {
        let var = if let Some(var) = self.free_vars.pop() {
            var
        } else {
            let idx = self.next_var;
            self.next_var += 1;
            Var(idx)
        };

        // TODO watches
        var_map_insert(&mut self.assigns, var, Default::default(), Default::default());
        var_map_insert(&mut self.vardata, var, Default::default(), Default::default());
        var_map_insert(&mut self.activity, var, 
                       if self.params.rnd_init_act {
                           drand(self.params.random_seed) * 0.00001
                       } else {
                           0.0
                       }, 0.0);
        var_map_insert(&mut self.seen, var, Default::default(), Default::default());
        var_map_insert(&mut self.polarity, var, 1, 1);
        var_map_insert(&mut self.user_pol, var, user_polarity, Default::default());
        self.decision.resize(var.0 as usize + 1, 1);
        // trail.capacity(v+1) // not needed?

        Lit(var.0) // TODO
    }
}

fn var_map_insert<T :Default + Clone>(map :&mut Vec<T>, Var(idx) :Var, value :T, default :T) {
    map.resize(idx as usize + 1, default);
    map[idx as usize] = value;
}

fn drand(seed :f64) -> f64 { unimplemented!() }

fn main() {
    println!("Hello, world!");
}
