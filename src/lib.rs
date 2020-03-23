use bitfield::bitfield;
use log::{debug, info, trace};
use std::io::Write;

// theory
//

#[derive(Copy, Clone)]
pub enum Check {
    Assert,
    Propagate,
    Final,
}

pub struct Refinement {
    last_clause_idx: i32,
    data: Vec<i32>,
}

impl Refinement {
    pub fn new() -> Self {
        Refinement {
            last_clause_idx: -1,
            data: Vec::new(),
        }
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.last_clause_idx = -1;
    }

    pub fn new_clause(&mut self) {
        self.last_clause_idx = self.data.len() as i32;
        self.data.push(0);
    }

    pub fn add_deduced(&mut self, lit: Lit, rref: u32) {
        self.data.push(-1);
        self.data.push(lit.0);
        self.data.push(rref as i32);
        self.last_clause_idx = -1;
    }

    pub fn add_clause_lit(&mut self, lit: Lit) {
        assert!(self.last_clause_idx >= 0 && self.last_clause_idx < self.data.len() as i32);
        self.data[self.last_clause_idx as usize] += 1;
        self.data.push(lit.0);
    }
}

//pub enum Refinement {
//    DeducedLit(Lit, u32),
//    NewClause(u32), // length
//    ClauseLit(
//}
//
//pub enum Refinement {
//    NewClause,
//    DeducedLit(Lit, u32),
//}

pub trait Theory {
    fn check(&mut self, ch: Check, new_lits: &[Lit], refinement: &mut Refinement);
    fn explain(&mut self, lit: Lit, lref: u32, refinement: &mut Refinement);
    fn new_decision_level(&mut self);
    fn backtrack(&mut self, n: i32);
}

pub struct NullTheory {}
impl Theory for NullTheory {
    fn check(&mut self, _: Check, _: &[Lit], _: &mut Refinement) {}
    fn explain(&mut self, _: Lit, _: u32, _: &mut Refinement) {} // unreachable
    fn new_decision_level(&mut self) {}
    fn backtrack(&mut self, _: i32) {}
}

pub struct SatSolver {
    pub prop: Solver<NullTheory>,
}

impl SatSolver {
    pub fn new() -> Self {
        SatSolver {
            prop: Solver::new(NullTheory {}),
        }
    }
}

// ------
// Variables and literals
// ------

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var(pub i32);
const VAR_UNDEF: Var = Var(-1);

impl Var {
    fn idx(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit(pub i32);

impl Lit {
    pub fn new(Var(var): Var, sign: bool) -> Lit {
        Lit(2 * var + sign as i32)
    }

    pub fn sign(&self) -> bool {
        ((self.0) & 1) != 0
    }

    pub fn var(&self) -> Var {
        Var(self.0 >> 1)
    }

    pub fn inverse(&self) -> Lit {
        Self::new(self.var(), !self.sign())
    }
}

pub const LIT_UNDEF: Lit = Lit(-2);
pub const LIT_ERROR: Lit = Lit(-1);

//#[repr(u8)]
//#[derive(Debug)]
//#[derive(Copy, Clone, PartialEq, Eq)]
//pub enum LBool {
//    False = 0,
//    True = 1,
//    Undef = 2,
//}

#[derive(Debug, Copy, Clone)]
pub struct LBool(u8);

impl PartialEq for LBool {
    fn eq(&self, rhs: &LBool) -> bool {
        ((rhs.0 & 2) & (self.0 & 2)) != 0 || (((rhs.0 & 2) == 0) && rhs.0 == self.0)
    }
}

pub const LBOOL_TRUE: LBool = LBool(0);
pub const LBOOL_FALSE: LBool = LBool(1);
pub const LBOOL_UNDEF: LBool = LBool(2);

impl LBool {
    fn xor(&self, b: bool) -> LBool {
        //trace!("xor {} ^ {} = {}", self.0, (b as u8), self.0 ^ (b as u8));
        LBool(self.0 ^ (b as u8))
        //unsafe { std::mem::transmute((*self as u8) ^ (b as u8)) }
    }
    fn from_bool(b: bool) -> LBool {
        LBool(b as u8)
        //unsafe { std::mem::transmute(b) }
    }
}

impl Default for LBool {
    fn default() -> Self {
        LBOOL_UNDEF
    }
}

// TODO &&, ||

bitfield! {
    pub struct ClauseHeader(u32);
    impl Debug;
    get_mark, set_mark :1, 0;
    get_learnt, set_learnt :2;
    get_extra_data, set_extra_data :3;
    get_reloced, set_reloced :4;
    get_size, set_size :31, 5;
}

type ClauseHeaderOffset = i32;
const CLAUSE_NONE: ClauseHeaderOffset = -1;
const CLAUSE_THEORY_UNDEF: ClauseHeaderOffset = -2;
const CLAUSE_THEORY_REFERENCE: ClauseHeaderOffset = -3;

type VMap<T> = Vec<T>;

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
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
struct Watcher {
    cref: ClauseHeaderOffset,
    blocker: Lit,
}

struct OrderHeap {
    heap: Vec<Var>,
    indices: VMap<i32>,
}

impl OrderHeap {
    pub fn build(&mut self, ns: &[i32], act: &[f64]) {
        for i in 0..self.heap.len() {
            self.indices[self.heap[i].0 as usize] = -1;
        }
        self.heap.clear();

        for i in 0..ns.len() {
            assert!(self.indices.len() > ns[i] as usize);
            self.indices[ns[i] as usize] = i as i32;
            self.heap.push(Var(ns[i]));
        }

        let mut i = (self.heap.len() / 2 - 1) as i32;
        while i >= 0 {
            self.percolate_down(i as i32, act);
            i -= 1;
        }
    }

    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

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
        trace!("percolate up i={},x={},p={}", i, var.0, p);
        //info!("act x {} heap[p] {}", act[var.0 as usize, act[self.heap[p as usize].0 as usize]);
        while i != 0 && act[var.0 as usize] > act[self.heap[p as usize].0 as usize] {
            self.heap[i as usize] = self.heap[p as usize];
            self.indices[self.heap[p as usize].0 as usize] = i;
            i = p;
            p = Self::parent(p);
            trace!("percolate up i={},x={},p={}", i, var.0, p);
        }

        self.heap[i as usize] = var;
        self.indices[var.0 as usize] = i;
        trace!("percolate done i={},x={},p={}", i, var.0, p);
    }

    pub fn percolate_down(&mut self, mut i: i32, act: &[f64]) {
        let var = self.heap[i as usize];
        while (Self::left(i) as usize) < self.heap.len() {
            let child = if (Self::right(i) as usize) < self.heap.len()
                && act[self.heap[Self::right(i) as usize].0 as usize]
                    > act[self.heap[Self::left(i) as usize].0 as usize]
            {
                Self::right(i)
            } else {
                Self::left(i)
            };

            if !(act[self.heap[child as usize].0 as usize] > act[var.0 as usize]) {
                break;
            }

            self.heap[i as usize] = self.heap[child as usize];
            self.indices[self.heap[i as usize].0 as usize] = i;
            i = child;
        }

        self.heap[i as usize] = var;
        self.indices[var.0 as usize] = i;
    }

    pub fn contains(&self, var: Var) -> bool {
        //debug!(" --> ORDER_HEAP CONTAINS({:?})", var);
        //info!("orderheap {:?}", self.indices);
        //dbg!(var.idx() < self.indices.len());
        var.idx() < self.indices.len() && self.indices[var.idx()] >= 0
    }

    pub fn decrease(&mut self, key: Var, act: &[f64]) {
        debug_assert!(self.contains(key));
        self.percolate_up(self.indices[key.0 as usize], act);
    }

    #[allow(unused)] // used in preprocessing, which is not implemented yet
    pub fn increase(&mut self, key: Var, act: &[f64]) {
        debug_assert!(self.contains(key));
        self.percolate_down(self.indices[key.0 as usize], act);
    }

    #[allow(unused)] // used in preprocessing, which is not implemented yet
    pub fn update(&mut self, key: Var, act: &[f64]) {
        if !self.contains(key) {
            self.insert(key, act);
        } else {
            self.percolate_up(self.indices[key.0 as usize], act);
            self.percolate_down(self.indices[key.0 as usize], act);
        }
    }

    pub fn insert(&mut self, key: Var, act: &[f64]) {
        //trace!("OrderHeap.insert key{:?}", key);
        self.indices
            .resize((key.0 as usize + 1).max(self.indices.len()), -1);
        //trace!("indices {:?}", self.indices);
        debug_assert!(!self.contains(key));

        self.indices[key.0 as usize] = self.heap.len() as i32;
        self.heap.push(key);
        self.percolate_up(self.indices[key.0 as usize], act);
    }

    //pub fn remove(&mut self, key: Var, act: &[f64]) {
    //    debug_assert!(self.contains(key));
    //    let k_pos = self.indices[key.0 as usize];
    //    self.indices[key.0 as usize] = -1;

    //    if k_pos < self.heap.len() as i32 - 1 {
    //        self.heap[k_pos as usize] = self.heap[self.heap.len() - 1];
    //        self.indices[self.heap[k_pos as usize].0 as usize] = k_pos;
    //        self.heap.pop();
    //        self.percolate_down(k_pos, act);
    //    } else {
    //        self.heap.pop();
    //    }
    //}

    pub fn remove_min(&mut self, act: &[f64]) -> Var {
        let var = self.heap[0];
        self.heap[0] = self.heap[self.heap.len() - 1];
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
    wasted: u32,
}

impl ClauseDatabase {
    fn relocate_clause(
        &mut self,
        cref: ClauseHeaderOffset,
        new_data: &mut Vec<u32>,
    ) -> ClauseHeaderOffset {
        let header = self.get_header(cref);
        if header.get_reloced() {
            return *self.get_relocated_address(cref);
        }

        // copy
        let size_in_u32 = 1 + header.get_size() as usize + header.get_extra_data() as usize;
        let new_addr = new_data.len() as ClauseHeaderOffset;
        new_data.extend(&self.clause_data[cref as usize..(cref as usize + size_in_u32)]);

        // mark the old clause
        self.get_header_mut(cref).set_reloced(true);
        *self.get_relocated_address(cref) = new_addr;

        // return new address
        new_addr
    }

    fn update_size(&mut self, cref: ClauseHeaderOffset, new_size: usize) {
        let mut header = self.get_header(cref);
        if header.get_extra_data() {
            let activity_addr = self.get_activity_address(cref);
            self.clause_data[cref as usize + 1 + new_size] = self.clause_data[activity_addr];
        }
        header.set_size(new_size as u32);
        *self.get_header_mut(cref) = header;
    }

    fn free(&mut self, cref: ClauseHeaderOffset) {
        let header = self.get_header(cref);
        self.wasted += 1 + header.get_size() + header.get_extra_data() as u32;
    }

    fn add_clause(&mut self, lits: &[Lit], learnt: bool) -> ClauseHeaderOffset {
        //let header_size = std::mem::size_of::<ClauseHeader>();
        let data_size = lits.len();

        let mut header = ClauseHeader(0);
        //println!("setting size to {}", data_size as u32);
        header.set_size(data_size as u32);
        header.set_learnt(learnt);
        header.set_extra_data(learnt); // TODO or extra clause field for simplification
        let header = header;

        let cref = self.clause_data.len() as i32;
        self.clause_data
            .push(unsafe { std::mem::transmute::<ClauseHeader, u32>(header) });

        //println!("setting raw data {:?}", lits);
        self.clause_data.extend(unsafe {
            std::slice::from_raw_parts(lits.as_ptr() as *const Lit as *const u32, lits.len())
        });

        if learnt {
            self.clause_data
                .push(unsafe { std::mem::transmute::<f32, u32>(0.0) });
        }

        //println!("db: {:?}", self.clause_data);

        cref
    }

    fn get_activity_address(&self, header_addr: ClauseHeaderOffset) -> usize {
        let header = self.get_header(header_addr);
        assert!(header.get_extra_data());
        assert!(header.get_learnt());

        header_addr as usize + 1 + header.get_size() as usize
    }

    fn get_activity<'a>(&'a self, header_addr: ClauseHeaderOffset) -> &'a f32 {
        let addr = self.get_activity_address(header_addr);
        unsafe { std::mem::transmute(&self.clause_data[addr]) }
    }

    fn get_activity_mut<'a>(&'a mut self, header_addr: ClauseHeaderOffset) -> &'a mut f32 {
        let header = self.get_header(header_addr);
        assert!(header.get_extra_data());
        assert!(header.get_learnt());
        unsafe {
            let ptr = (self.clause_data.get_mut(header_addr as usize).unwrap() as *mut u32
                as *mut f32)
                //.offset((1 + header.get_size()) as isize * std::mem::size_of::<u32>() as isize);
                .offset(1 + header.get_size() as isize);
            &mut *ptr
        }
    }

    fn get_clause_mut<'a>(
        &'a mut self,
        header_addr: ClauseHeaderOffset,
    ) -> (&'a mut ClauseHeader, &'a mut [Lit]) {
        assert!(header_addr >= 0);
        assert_eq!(
            std::mem::size_of::<ClauseHeader>(),
            std::mem::size_of::<u32>()
        );
        let val = &mut self.clause_data[header_addr as usize];
        let header = unsafe { std::mem::transmute::<&mut u32, &mut ClauseHeader>(val) };
        let size = header.get_size() as usize;
        let lits = unsafe {
            let ptr = (self.clause_data.get_mut(header_addr as usize).unwrap() as *mut u32
                as *mut Lit)
                //.offset(std::mem::size_of::<ClauseHeader>() as isize);
                .offset(1); //std::mem::size_of::<ClauseHeader>() as isize);
            std::slice::from_raw_parts_mut(ptr, size)
        };
        (header, lits)
    }

    fn get_header_mut<'a>(&'a mut self, header_addr: ClauseHeaderOffset) -> &'a mut ClauseHeader {
        assert!(header_addr >= 0);
        assert_eq!(
            std::mem::size_of::<ClauseHeader>(),
            std::mem::size_of::<u32>()
        );
        let val = &mut self.clause_data[header_addr as usize];
        unsafe { std::mem::transmute::<&mut u32, &mut ClauseHeader>(val) }
    }

    fn get_header(&self, header_addr: ClauseHeaderOffset) -> ClauseHeader {
        //info!("get header {}/{}", header_addr, self.clause_data.len());
        assert!(header_addr >= 0);
        assert_eq!(
            std::mem::size_of::<ClauseHeader>(),
            std::mem::size_of::<u32>()
        );
        let val = self.clause_data[header_addr as usize];
        let h = unsafe { std::mem::transmute::<u32, ClauseHeader>(val) };
        //println!("Header {:?}", h);
        h
    }

    fn get_lits<'a>(&'a self, header_addr: ClauseHeaderOffset, size: usize) -> &'a [Lit] {
        //println!("getting lits from {}..+{}", header_addr, size);
        //let offset = std::mem::size_of::<ClauseHeader>() as isize;
        //println!("offset {:?}", offset);
        unsafe {
            let ptr =
                (&self.clause_data[header_addr as usize] as *const u32 as *const Lit).offset(1);
            std::slice::from_raw_parts(ptr, size)
        }
    }

    fn get_relocated_address<'a>(
        &'a mut self,
        header_addr: ClauseHeaderOffset,
    ) -> &mut ClauseHeaderOffset {
        unsafe {
            let ptr = (self.clause_data.get_mut(header_addr as usize).unwrap() as *mut u32
                as *mut ClauseHeaderOffset)
                //.offset(std::mem::size_of::<ClauseHeader>() as isize);
                .offset(1); //std::mem::size_of::<ClauseHeader>() as isize);
            &mut *ptr
        }
    }

    fn get_lits_mut<'a>(
        &'a mut self,
        header_addr: ClauseHeaderOffset,
        size: usize,
    ) -> &'a mut [Lit] {
        unsafe {
            let ptr = (self.clause_data.get_mut(header_addr as usize).unwrap() as *mut u32
                as *mut Lit)
                //.offset(std::mem::size_of::<ClauseHeader>() as isize);
                .offset(1); //std::mem::size_of::<ClauseHeader>() as isize);
            std::slice::from_raw_parts_mut(ptr, size)
        }
    }
}

pub struct Solver<Theory> {
    theory: Theory,
    pub tracelog_file: Option<std::io::BufWriter<std::fs::File>>,

    pub verbosity: u32,
    // Extra results (read-only for consumer)
    pub model: Vec<LBool>,
    pub conflict: Vec<Lit>,

    pub params: SolverParams,
    pub stats: SolverStatistics,

    // solver state
    clause_database: ClauseDatabase,
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
    theory_qhead: usize,
    theory_refinement_buffer: Refinement,

    simp_db_assigns: i32,
    simp_db_props: i64,
    // TODO
    //progress_estimate: f64,
    remove_satisfied: bool,
    next_var: i32,

    released_vars: Vec<Var>,
    free_vars: Vec<Var>,
    seen: VMap<i8>,
    analyze_stack: Vec<ShrinkStackElem>,
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

impl<Theory: crate::Theory> Solver<Theory> {
    pub fn num_vars(&self) -> usize {
        self.next_var as usize
    }
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }
    pub fn new(theory: Theory) -> Self {
        Solver {
            theory: theory,
            tracelog_file: None,
            verbosity: 1,
            watch_occs: Vec::new(),
            watch_dirty: Vec::new(),
            watch_dirties: Vec::new(),

            clause_database: ClauseDatabase {
                clause_data: Vec::new(),
                wasted: 0,
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
            theory_qhead: 0,
            theory_refinement_buffer: Refinement::new(),
            simp_db_assigns: -1,
            simp_db_props: 0,
            //progress_estimate: 0.0,
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
        self.decision
            .resize((var.0 as usize + 1).max(self.decision.len()), 0);
        self.set_decision_var(var, decision_var);
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
        self.var_inc *= 1.0 / self.params.var_decay;
    }

    fn var_bump_activity(
        activity: &mut [f64],
        order_heap: &mut OrderHeap,
        var_inc: &mut f64,
        var: Var,
        inc: f64,
    ) {
        activity[var.0 as usize] += inc;
        if activity[var.0 as usize] > 1e100 {
            // rescale
            for act in activity.iter_mut() {
                *act *= 1e-100;
            }
            *var_inc *= 1e-100;
        }

        // update heap
        trace!("heap min before varbump {}", order_heap.heap[0].0);
        trace!("contains {:?}", order_heap.contains(var));
        if order_heap.contains(var) {
            order_heap.decrease(var, &*activity);
        }
        trace!("heap min after  varbump {}", order_heap.heap[0].0);
    }

    fn clause_decay_activity(&mut self) {
        self.cla_inc *= 1.0 / self.params.clause_decay;
    }

    fn clause_bump_activity(&mut self, cref: ClauseHeaderOffset) {
        let activity = self.clause_database.get_activity_mut(cref);
        *activity += self.cla_inc as f32;
        if *activity > 1e20 {
            // rescale
            for p in self.learnts.iter() {
                *self.clause_database.get_activity_mut(*p) *= 1e-20;
            }
            self.cla_inc *= 1e-20;
        }
    }

    pub fn release_var(&mut self, l: Lit) {
        if self.lit_value(l) == LBOOL_UNDEF {
            self.add_clause(std::iter::once(l));
            self.released_vars.push(l.var());
        }
    }

    fn var_value(&self, var: Var) -> LBool {
        self.assigns[var.0 as usize]
    }

    fn lit_value(&self, lit: Lit) -> LBool {
        Self::assigns_lit_value(&self.assigns, lit)
    }

    fn assigns_lit_value(assigns: &Vec<LBool>, lit: Lit) -> LBool {
        LBool::xor(&assigns[lit.var().0 as usize], lit.sign())
    }

    pub fn add_clause(&mut self, ps: impl Iterator<Item = Lit>) -> bool {
        // Add "original" clause, cannot be directly used
        // during search because of simplification.
        assert!(self.trail_lim.len() == 0);
        if !self.ok {
            return false;
        }

        self.add_tmp.clear();
        self.add_tmp.extend(ps);
        self.add_tmp.sort();
        {
            let mut prev = LIT_UNDEF;
            let mut already_sat = false;
            let add_tmp = &mut self.add_tmp;
            let assigns = &self.assigns;
            add_tmp.retain(|l| {
                if Self::assigns_lit_value(assigns, *l) == LBOOL_FALSE || *l == prev.inverse() {
                    already_sat = true;
                }
                !(/* dedup */(prev, prev=*l).0 == *l
                  || /* known */ Self::assigns_lit_value(assigns, *l) == LBOOL_TRUE)
            });

            if already_sat {
                return true;
            }
        }

        if self.add_tmp.len() == 0 {
            self.ok = false;
            return false;
        } else if self.add_tmp.len() == 1 {
            self.unchecked_enqueue(self.add_tmp[0], CLAUSE_NONE);
            self.ok = self.propagate_bool() == CLAUSE_NONE;
            return self.ok;
        } else {
            let cref = self.clause_database.add_clause(&self.add_tmp, false);
            self.clauses.push(cref);
            self.attach_clause(cref);
        }

        true
    }

    fn attach_clause(&mut self, cref: ClauseHeaderOffset) {
        let header = self.clause_database.get_header(cref);
        let sz = header.get_size();
        assert!(sz > 1);

        let lits = self.clause_database.get_lits(cref, sz as usize);
        //println!("attaching {:?}", lits);
        //println!(" 0.inv {:?}", lits[0].inverse());
        //println!(" 0.inv {:?}", lits[0].inverse().0 as usize);
        //println!("");

        if header.get_learnt() {
            trace!(
                "watch {:?} -> {:?} (cr={})",
                lits[0].inverse(),
                lits[1],
                cref
            );
            trace!(
                "watch {:?} -> {:?} (cr={})",
                lits[1].inverse(),
                lits[0],
                cref
            );
        }

        self.watch_occs[lits[0].inverse().0 as usize].push(Watcher {
            cref,
            blocker: lits[1],
        });
        self.watch_occs[lits[1].inverse().0 as usize].push(Watcher {
            cref,
            blocker: lits[0],
        });

        if header.get_learnt() {
            self.stats.num_learnts += 1;
            self.stats.learnts_literals += sz as usize;
        } else {
            self.stats.num_clauses += 1;
            self.stats.clauses_literals += sz as usize;
        }
    }

    fn detach_clause(&mut self, cref: ClauseHeaderOffset, strict: bool) {
        let header = self.clause_database.get_header(cref);
        let sz = header.get_size();
        assert!(sz > 1);
        let lits = self.clause_database.get_lits(cref, sz as usize);

        if strict {
            self.watch_occs[lits[0].inverse().0 as usize].retain(|w| {
                w != &Watcher {
                    cref,
                    blocker: lits[1],
                }
            });
            self.watch_occs[lits[1].inverse().0 as usize].retain(|w| {
                w != &Watcher {
                    cref,
                    blocker: lits[0],
                }
            });
        } else {
            Self::smudge_watcher(
                &mut self.watch_dirty,
                &mut self.watch_dirties,
                lits[0].inverse(),
            );
            Self::smudge_watcher(
                &mut self.watch_dirty,
                &mut self.watch_dirties,
                lits[1].inverse(),
            );
        }

        if header.get_learnt() {
            self.stats.num_learnts -= 1;
            self.stats.learnts_literals -= sz as usize;
        } else {
            self.stats.num_clauses -= 1;
            self.stats.clauses_literals -= sz as usize;
        }
    }

    fn smudge_watcher(dirty: &mut Vec<i8>, dirties: &mut Vec<Lit>, lit: Lit) {
        let flag = &mut dirty[lit.0 as usize];
        if *flag == 0 {
            *flag = 1;
            dirties.push(lit);
        }
    }

    fn remove_clause(&mut self, cref: ClauseHeaderOffset) {
        self.detach_clause(cref, false);
        let header = self.clause_database.get_header(cref);
        let lits = self
            .clause_database
            .get_lits(cref, header.get_size() as usize);

        if self.is_clause_locked(cref, lits) {
            let vardata = &mut self.vardata[lits[0].var().0 as usize];
            vardata.reason = CLAUSE_NONE;
        }

        self.clause_database.get_header_mut(cref).set_mark(1 as u32);
        self.clause_database.free(cref);
    }

    fn is_clause_locked(&self, cref: ClauseHeaderOffset, lits: &[Lit]) -> bool {
        let vardata = &self.vardata[lits[0].var().0 as usize];
        self.lit_value(lits[0]) == LBOOL_TRUE
            && vardata.reason != CLAUSE_NONE
            && vardata.reason == cref
    }

    //fn satisfied(&self, clause: &[Lit]) -> bool {
    //    clause.iter().any(|l| self.lit_value(*l) == LBOOL_TRUE)
    //}

    fn assigns_satisfied(assigns: &Vec<LBool>, clause: &[Lit]) -> bool {
        clause
            .iter()
            .any(|l| Self::assigns_lit_value(assigns, *l) == LBOOL_TRUE)
    }

    fn cancel_until(&mut self, level: i32) {
        trace!(" --> CANCEL_UNTIL(level={})", level);
        if self.trail_lim.len() > level as usize {
            let mut c = (self.trail.len() - 1) as i32;
            while c >= self.trail_lim[level as usize] {
                let x = self.trail[c as usize];
                self.assigns[x.var().0 as usize] = LBOOL_UNDEF;
                if self.params.phase_saving > 1
                    || (self.params.phase_saving == 1 && Some(&c) > self.trail_lim.last())
                {
                    self.polarity[x.var().0 as usize] = x.sign() as i8;
                }
                trace!(
                    "The decision var was {:?}/{:?}, putting it back into the queue",
                    x,
                    x.var()
                );
                self.insert_var_order(x.var());
                c -= 1;
            }

            trace!(
                "qhead {} -> {}",
                self.qhead,
                self.trail_lim[level as usize] as usize
            );
            self.qhead = self.trail_lim[level as usize] as usize;
            self.theory_qhead = self.qhead;
            let l1 = self.trail.len();
            self.trail.truncate(self.trail_lim[level as usize] as usize);
            trace!("traillen {} -> {}", l1, self.trail.len());
            let l2 = self.trail_lim.len();
            self.trail_lim.truncate(level as usize);
            trace!("traillen {} -> {}", l2, self.trail_lim.len());

            self.theory.backtrack(level);
        }
    }

    fn pick_branch_lit(&mut self) -> Lit {
        let mut next = VAR_UNDEF;

        // random
        if drand(&mut self.params.random_seed) < self.params.random_var_freq
            && !self.order_heap.is_empty()
        {
            next = self.order_heap.heap[irand(
                &mut self.params.random_seed,
                self.order_heap.heap.len() as i32,
            ) as usize];
            if self.var_value(next) == LBOOL_UNDEF && self.decision[next.0 as usize] == 1 {
                self.stats.rnd_decisions += 1;
            }
        }

        // activity-based
        while next == VAR_UNDEF
            || self.var_value(next) != LBOOL_UNDEF
            || self.decision[next.0 as usize] == 0
        {
            if self.order_heap.is_empty() {
                next = VAR_UNDEF;
                break;
            } else {
                trace!("order_heap.remove_min {}", self.order_heap.heap[0].0);
                next = self.order_heap.remove_min(&self.activity);
            }
        }

        // polarity
        if next == VAR_UNDEF {
            LIT_UNDEF
        } else if self.user_pol[next.0 as usize] != LBOOL_UNDEF {
            Lit::new(next, self.user_pol[next.0 as usize] == LBOOL_TRUE)
        } else if self.params.rnd_pol {
            Lit::new(next, drand(&mut self.params.random_seed) < 0.5)
        } else {
            Lit::new(next, self.polarity[next.0 as usize] == 1)
        }
    }

    /// Analyze conflict and produce a reason lcause.
    ///
    /// Pre-conditions:
    /// * out_learnt is assumed to be empty.
    /// * Current decision level must be greater than root level.
    ///
    /// Post-conditions:
    /// * out_learnt[0] is the asserting literal at the returned backtracking level.
    /// * if out_learnt.len() > 1 then out_learnt[1] has the greatest decision
    ///   level of the rest of the literals.
    fn analyze(
        &mut self,
        mut conflict_clause: ClauseHeaderOffset,
        out_learnt: &mut Vec<Lit>,
    ) -> i32 {
        trace!("--> ANALYZE cref{}", conflict_clause);
        let mut path_c = 0;
        let mut p = LIT_UNDEF;
        out_learnt.push(Lit(0));
        let mut index = self.trail.len() - 1;

        loop {
            trace!("index_a {}", index);
            trace!("   (analyze clause {})", conflict_clause);
            assert!(conflict_clause != CLAUSE_NONE);
            let header = self.clause_database.get_header(conflict_clause);
            if header.get_learnt() {
                assert!(header.get_extra_data());
                self.clause_bump_activity(conflict_clause);
            } else {
                trace!("conflict is orig clause");
            }

            let lits = self
                .clause_database
                .get_lits(conflict_clause, header.get_size() as usize);
            for q in lits.iter().skip(if p == LIT_UNDEF { 0 } else { 1 }) {
                trace!("q {}", q.0);
                if self.seen[q.var().idx()] == 0 && self.vardata[q.var().idx()].level > 0 {
                    let inc = self.var_inc;
                    Self::var_bump_activity(
                        &mut self.activity,
                        &mut self.order_heap,
                        &mut self.var_inc,
                        q.var(),
                        inc,
                    );
                    self.seen[q.var().idx()] = 1;
                    if self.vardata[q.var().idx()].level >= self.trail_lim.len() as i32 {
                        path_c += 1;
                    } else {
                        out_learnt.push(*q);
                    }
                }
            }

            // select next clause to look at:
            trace!("index_c {}", index);
            loop {
                index -= 1;
                if self.seen[self.trail[index + 1].var().idx()] != 0 {
                    break;
                }
            }
            trace!("index_b {}", index);
            p = self.trail[index + 1];
            conflict_clause = self.get_reason(p.var());
            self.seen[p.var().idx()] = 0;
            path_c -= 1;

            if path_c <= 0 {
                break;
            }
        }

        out_learnt[0] = p.inverse();
        trace!("ANALYZE TRACED out learnt {:?}", out_learnt);

        // simplify conflict clause

        self.analyze_toclear.clear();
        self.analyze_toclear.resize(out_learnt.len(), LIT_UNDEF);
        self.analyze_toclear.copy_from_slice(out_learnt.as_slice());

        self.stats.max_literals += out_learnt.len();
        if self.params.ccmin_mode == 2 {
            let first = out_learnt[0];
            out_learnt.retain(|l| {
                *l == first
                    || self.vardata[l.var().idx()].reason == CLAUSE_NONE
                    || !self.lit_redundant(*l)
            });
        } else if self.params.ccmin_mode == 1 {
            // TODO is this mode used?
            unimplemented!()
        }
        self.stats.tot_literals += out_learnt.len();

        trace!("ANALYZE SIMPLIFIED to  {:?}", out_learnt);

        // find correct backtrack level
        let out_level = if out_learnt.len() == 1 {
            0
        } else {
            let mut max_idx = 1;
            let mut max_level = self.vardata[out_learnt[1].var().idx()].level;
            let mut i = 2;
            while i < out_learnt.len() {
                let lit_level = self.vardata[out_learnt[i].var().idx()].level;
                if lit_level > max_level {
                    max_idx = i;
                    max_level = lit_level;
                }
                i += 1;
            }

            out_learnt.swap(1, max_idx);
            self.vardata[out_learnt[1].var().idx()].level
        };

        for l in self.analyze_toclear.iter() {
            self.seen[l.var().idx()] = 0;
        }

        out_level
    }

    fn lit_redundant(&mut self, p: Lit) -> bool {
        trace!(" --> LIT REDUNDANT?");
        #[repr(i8)]
        enum Seen {
            Undef = 0,
            Source = 1,
            Removable = 2,
            Failed = 3,
        }

        assert!(
            self.seen[p.var().idx()] == Seen::Undef as i8
                || self.seen[p.var().idx()] == Seen::Source as i8
        );
        assert!(self.vardata[p.var().idx()].reason != CLAUSE_NONE);

        self.analyze_stack.clear();

        let mut i = 0;
        let mut p = p;
        'outer: loop {
            i += 1;
            trace!(" lit redundant i={}", i);

            //let reason = self.vardata[p.var().idx()].reason;
            let reason = self.get_reason(p.var());
            let header = self.clause_database.get_header(reason);
            let lits = self
                .clause_database
                .get_lits(reason, header.get_size() as usize);

            if i < header.get_size() {
                // checking 'p'-parents 'l':
                let l = lits[i as usize];

                // variable at level 0 or previously removable
                if self.vardata[l.var().idx()].level == 0
                    || self.seen[l.var().idx()] == Seen::Source as i8
                    || self.seen[l.var().idx()] == Seen::Removable as i8
                {
                    continue;
                }

                // Check variable can not be removed for some local reason
                let local_reason = self.get_reason(l.var()); // TODO why is this call allowed when lits is borrowed?
                if local_reason == CLAUSE_NONE
                    || self.seen[l.var().idx()] == Seen::Failed as i8
                {
                    self.analyze_stack.push(ShrinkStackElem { i: 0, l: p });
                    for elem in self.analyze_stack.iter() {
                        if self.seen[elem.l.var().idx()] == Seen::Undef as i8 {
                            self.seen[elem.l.var().idx()] = Seen::Failed as i8;
                            self.analyze_toclear.push(elem.l);
                        }
                    }

                    trace!(" --> LIT REDUNDANT: no ");
                    return false;
                }

                // recursively check 'l':
                self.analyze_stack.push(ShrinkStackElem { i: i, l: p });
                i = 0;
                p = l;
            } else {
                // finished with current element 'p' and reason 'c':
                if self.seen[p.var().idx()] == Seen::Undef as i8 {
                    self.seen[p.var().idx()] = Seen::Removable as i8;
                    self.analyze_toclear.push(p);
                }

                if let Some(elem) = self.analyze_stack.pop() {
                    i = elem.i;
                    p = elem.l;
                } else {
                    trace!(" --> LIT REDUNDANT: yes ");
                    return true; // success if stack is empty
                }
            }
        }
    }

    fn analyze_final(&mut self, p: Lit) {
        // TODO here we have just a vec of lits, instead of minisat's redundant intmap+vec structure
        self.conflict.clear();
        self.conflict.push(p);

        if self.trail_lim.len() == 0 {
            return;
        }

        self.seen[p.var().idx()] = 1;

        let mut i: usize = self.trail.len() - 1;
        while i >= self.trail_lim[0] as usize {
            let var = self.trail[i].var();
            if self.seen[var.idx()] > 0 {
                //let reason = self.vardata[var.idx()].reason;
                let reason = self.get_reason(var);
                if reason == CLAUSE_NONE {
                    assert!(self.vardata[var.idx()].level > 0);
                    self.conflict.push(self.trail[i].inverse());
                } else {
                    let header = self.clause_database.get_header(reason);
                    let lits = self
                        .clause_database
                        .get_lits(reason, header.get_size() as usize);
                    for l in lits.iter().skip(1) {
                        if self.vardata[l.var().idx()].level > 0 {
                            self.seen[l.var().idx()] = 1;
                        }
                    }
                }
            }
            i -= 1;
        }

        self.seen[p.var().idx()] = 0;
    }

    fn unchecked_enqueue(&mut self, lit: Lit, reason: ClauseHeaderOffset) {
        trace!("assign {}", lit.0);
        assert!(self.lit_value(lit) == LBOOL_UNDEF);
        self.assigns[lit.var().0 as usize] = LBool::from_bool(lit.sign());
        self.vardata[lit.var().0 as usize] = VariableData {
            reason,
            level: self.trail_lim.len() as i32,
        };
        self.trail.push(lit);
    }

    fn propagate_bool(&mut self) -> ClauseHeaderOffset {
        trace!("-> PROPAGATE");
        let mut conflict_clause = CLAUSE_NONE;
        let mut num_props = 0;

        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            trace!("Propagating {:?}", p);
            self.qhead += 1;

            self.clean_watch(p);

            num_props += 1;

            let (mut i, mut j) = (0, 0);
            'for_each_watch: while i < self.watch_occs[p.0 as usize].len() {
                let assigns = &self.assigns;
                let watches = &mut self.watch_occs[p.0 as usize];
                let blocker = watches[i].blocker;
                let cref = watches[i].cref;
                trace!("cref {}", cref);
                if Self::assigns_lit_value(assigns, blocker) == LBOOL_TRUE {
                    watches[j] = watches[i];
                    j += 1;
                    i += 1;
                    trace!("by blocker {:?}", blocker);
                    continue;
                }

                // Make sure the false literal is clause_lits[1].
                let header = self.clause_database.get_header(cref);
                let lits = self
                    .clause_database
                    .get_lits_mut(cref, header.get_size() as usize);
                let false_lit = p.inverse();
                if lits[0] == false_lit {
                    lits.swap(0, 1);
                }
                assert!(lits[1] == false_lit);

                i += 1;

                let first = lits[0];
                let w = Watcher {
                    cref: cref,
                    blocker: first,
                };
                // If 0th watch is true, then the clause is already satisfied
                if first != blocker && Self::assigns_lit_value(assigns, first) == LBOOL_TRUE {
                    watches[j] = w;
                    j += 1;
                    trace!("0th true {:?}", first);
                    continue;
                }

                trace!("looking for watch");
                // Look for new watch:
                let mut k = 2;
                while k < lits.len() {
                    trace!("look for watch in k{} {:?}", k, lits[k]);
                    if Self::assigns_lit_value(assigns, lits[k]) != LBOOL_FALSE {
                        lits[1] = lits[k];
                        lits[k] = false_lit;
                        self.watch_occs[lits[1].inverse().0 as usize].push(w);
                        trace!("new watch {:?} {:?}", w.cref, w.blocker);
                        continue 'for_each_watch;
                    } else {
                        k += 1;
                    }
                }
                trace!("did not find watch");

                // Did not find watch -- clause is unit under assignment:
                watches[j] = w;
                j += 1;
                if Self::assigns_lit_value(assigns, first) == LBOOL_FALSE {
                    trace!(
                        "found conflict {}/{}",
                        cref,
                        self.clause_database.clause_data.len()
                    );
                    trace!(
                        "original clause idx {:?}",
                        self.clauses.iter().position(|i| *i == cref)
                    );
                    //trace!("{:?}", self.clauses);
                    trace!(
                        "learnt   clause idx {:?}",
                        self.learnts.iter().position(|i| *i == cref)
                    );
                    conflict_clause = cref;
                    self.qhead = self.trail.len();
                    while i < self.watch_occs[p.0 as usize].len() {
                        self.watch_occs[p.0 as usize][j] = self.watch_occs[p.0 as usize][i];
                        j += 1;
                        i += 1;
                    }
                    trace!("copy remaining");
                } else {
                    self.unchecked_enqueue(first, cref);
                    trace!("enqueue {:?}", first);
                }
            }

            self.watch_occs[p.0 as usize].truncate(j);
        }
        trace!("propagated  {}", num_props);
        self.stats.propagations += num_props;
        self.simp_db_props -= num_props as i64;

        trace!("propagated {}", num_props);

        conflict_clause
    }

    fn reduce_db(&mut self) {
        let extra_lim = self.cla_inc / self.learnts.len() as f64;
        {
            use std::cmp::Ordering;
            let db = &self.clause_database;
            //info!("reduce_db sorted?");
            self.learnts.sort_by(|x, y| {
                //dbg!(db.get_header(*x));
                //dbg!(db.get_header(*y));
                //dbg!(db.get_activity(*x));
                //dbg!(db.get_activity(*y));
                if db.get_header(*x).get_size() > 2
                    && (db.get_header(*y).get_size() == 2
                        || db.get_activity(*x) < db.get_activity(*y))
                {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            });
            //info!("reduce_db sorted");
        }

        let (mut i, mut j) = (0, 0);
        while i < self.learnts.len() {
            let cref = self.learnts[i];
            let header = self.clause_database.get_header(cref);
            let lits = self
                .clause_database
                .get_lits(cref, header.get_size() as usize);
            if header.get_size() > 2
                && !self.is_clause_locked(cref, lits)
                && (i < self.learnts.len() / 2
                    || (*self.clause_database.get_activity(cref) as f64) < extra_lim)
            {
                self.remove_clause(cref);
            } else {
                // keep in self.learnts
                self.learnts[j] = cref;
                j += 1;
            }
            i += 1;
        }
        self.learnts.truncate(j);
        //info!("check garbage from reduce_db");
        self.check_garbage();
    }

    fn check_garbage(&mut self) {
        if (self.clause_database.wasted as f64)
            > (self.clause_database.clause_data.len() as f64) * self.params.garbage_frac
        {
            self.garbage_collect();
        }
    }

    fn garbage_collect(&mut self) {
        //panic!("garbage collect");
        let mut new_data = Vec::with_capacity(
            self.clause_database.clause_data.len() - self.clause_database.wasted as usize,
        );
        self.reloc_all_clauses(&mut new_data);
        std::mem::swap(&mut self.clause_database.clause_data, &mut new_data);
        self.clause_database.wasted = 0;
    }

    fn has_reason_clause(&self, var :Var) -> bool {
        self.vardata[var.idx()].reason >= 0
    }

    fn get_reason(&mut self, var :Var) -> ClauseHeaderOffset {
        self.vardata[var.idx()].reason
    }

    fn reloc_all_clauses(&mut self, new_data: &mut Vec<u32>) {
        //assert!(self.trail_lim.len() == 0);
        // TODO extra_clause_field

        self.clean_all_watches();

        // relocate watches
        for v in 0..(self.next_var) {
            for s in vec![false, true] {
                let p = Lit::new(Var(v as i32), s);
                let watches = &mut self.watch_occs[p.0 as usize];
                for w in watches.iter_mut() {
                    w.cref = self.clause_database.relocate_clause(w.cref, new_data);
                }
            }
        }
        //for ws in self.watch_occs.iter() {
        //    for w in ws.iter() {
        //        self.clause_database.relocate_clause(w.cref, new_data);
        //    }
        //}

        // relocate reasons
        for i in 0..self.trail.len() {
            let var = self.trail[i].var();
            if !self.has_reason_clause(var) { continue; }
            let reason = self.get_reason(var);
            if reason != CLAUSE_NONE {
                let header = self.clause_database.get_header(reason);
                let lits = self
                    .clause_database
                    .get_lits(reason, header.get_size() as usize);
                if header.get_reloced() || self.is_clause_locked(reason, lits) {
                    assert!(header.get_mark() != 1); // is not removed
                    let cl = &mut self.vardata[var.idx()].reason;
                    *cl = self.clause_database.relocate_clause(*cl, new_data);
                }
            }
        }

        // relocate learnt clauses
        let (mut i, mut j) = (0, 0);
        while i < self.learnts.len() {
            let header = self.clause_database.get_header(self.learnts[i]);
            if header.get_mark() != 1 {
                self.learnts[i] = self
                    .clause_database
                    .relocate_clause(self.learnts[i], new_data);
                self.learnts[j] = self.learnts[i];
                j += 1;
            }
            i += 1;
        }
        self.learnts.truncate(j);

        // relocate original clauses
        let (mut i, mut j) = (0, 0);
        while i < self.clauses.len() {
            let header = self.clause_database.get_header(self.clauses[i]);
            if header.get_mark() != 1 {
                self.clauses[i] = self
                    .clause_database
                    .relocate_clause(self.clauses[i], new_data);
                self.clauses[j] = self.clauses[i];
                j += 1;
            }
            i += 1;
        }
        self.clauses.truncate(j);
    }

    fn remove_satisfied(&mut self, clauses: &mut Vec<ClauseHeaderOffset>) {
        debug!("--> REMOVE_SATISFIED");
        let (mut i, mut j) = (0, 0);
        while i < clauses.len() {
            let cref = clauses[i];
            let (header, lits) = self.clause_database.get_clause_mut(cref);
            //trace!("lits: {:?}", lits);
            //trace!("all undef: {:?}", self.assigns.iter().all(|a| *a == LBOOL_UNDEF));
            if Self::assigns_satisfied(&self.assigns, lits) {
                self.remove_clause(cref);
            } else {
                assert!(
                    Self::assigns_lit_value(&self.assigns, lits[0]) == LBOOL_UNDEF
                        || Self::assigns_lit_value(&self.assigns, lits[1]) == LBOOL_UNDEF
                );
                let mut k: usize = 2;
                let mut new_len = header.get_size() as usize;
                while k < new_len {
                    if Self::assigns_lit_value(&self.assigns, lits[k]) == LBOOL_FALSE {
                        new_len -= 1;
                        lits[k] = lits[new_len];
                        k -= 1;
                    }
                    k += 1;
                }
                self.clause_database.update_size(cref, new_len);

                // keep
                clauses[j] = clauses[i];
                j += 1;
            }
            i += 1;
        }
        //trace!("truncate {}-{} {:?}", i, j, clauses );
        clauses.truncate(j);
        //trace!("truncate {:?}", clauses);
    }

    fn clean_all_watches(&mut self) {
        // TODO should not be necessary to reallocate here
        let dirties = std::mem::replace(&mut self.watch_dirties, Vec::new());
        for l in dirties {
            self.clean_watch(l);
        }
    }

    fn clean_watch(&mut self, lit: Lit) {
        if self.watch_dirty[lit.0 as usize] == 0 {
            return;
        }
        let db = &self.clause_database;
        self.watch_occs[lit.0 as usize].retain(|w| db.get_header(w.cref).get_mark() != 1);
        self.watch_dirty[lit.0 as usize] = 0;
    }

    fn simplify(&mut self) -> bool {
        assert!(self.trail_lim.len() == 0);
        debug!(
            "simplify called at decisionlevel=0 with trail length={}",
            self.trail.len()
        );
        if !self.ok || self.propagate_bool() != CLAUSE_NONE {
            self.ok = false;
            return false;
        }

        if (self.trail.len() as i32) == self.simp_db_assigns || self.simp_db_props > 0 {
            return true;
        }

        write!(self.tracelog_file.as_mut().unwrap(), "simp\n").unwrap();

        // TODO do not move/allocate here.
        debug!("remove satisfied learnt clauses ({})", self.learnts.len());
        let mut learnts = std::mem::replace(&mut self.learnts, Vec::new());
        self.remove_satisfied(&mut learnts);
        self.learnts = learnts;
        debug!("             --> learnt clauses ({})", self.learnts.len());
        if self.remove_satisfied {
            debug!("remove satisfied original clauses ({})", self.clauses.len());
            let mut clauses = std::mem::replace(&mut self.clauses, Vec::new());
            self.remove_satisfied(&mut clauses);
            self.clauses = clauses;
            debug!("             --> original clauses ({})", self.clauses.len());

            // remove released variables from trail
            for v in self.released_vars.iter() {
                assert!(self.seen[v.idx()] == 0);
                self.seen[v.idx()] = 1;
            }

            let seen = &mut self.seen;
            assert!(self.qhead == self.trail.len());
            self.trail.retain(|l| seen[l.var().idx()] == 0);
            self.qhead = self.trail.len();
            self.theory_qhead = self.qhead; // TODO does this work correctly with theory?
            for v in self.released_vars.iter() {
                self.seen[v.idx()] = 0;
            }
            self.free_vars.extend(self.released_vars.drain(..));
        }

        self.check_garbage();
        self.rebuild_order_heap();

        self.simp_db_assigns = self.trail.len() as i32;
        self.simp_db_props =
            self.stats.clauses_literals as i64 + self.stats.learnts_literals as i64;

        true
    }

    fn rebuild_order_heap(&mut self) {
        let mut vs = Vec::new();
        for v in 0..self.decision.len() {
            if self.decision[v] == 1 && self.var_value(Var(v as i32)) == LBOOL_UNDEF {
                vs.push(v as i32);
            }
        }
        self.order_heap.build(&vs, &self.activity);
    }

    fn propagate(&mut self) -> ClauseHeaderOffset {
        while self.qhead < self.trail.len() {
            let bool_prop = self.propagate_bool();
            if bool_prop != CLAUSE_NONE {
                return bool_prop;
            }
            assert!(self.qhead == self.trail.len()); // boolean prop finished without conflict

            let are_all_assigned = self.order_heap.is_empty() && self.qhead == self.trail.len();
            let check = if are_all_assigned {
                Check::Final
            } else {
                Check::Propagate
            };
            let new_lits = &self.trail[self.theory_qhead..self.trail.len()];
            self.theory_qhead = self.trail.len();
            self.theory_refinement_buffer.clear();
            self.theory
                .check(check, new_lits, &mut self.theory_refinement_buffer);
            let theory_conflict = self.theory_refinement();
            if theory_conflict != CLAUSE_NONE {
                return theory_conflict;
            }
        }

        CLAUSE_NONE
    }

    fn theory_refinement(&mut self) -> ClauseHeaderOffset {
        // first pass: push deductions to trail or convert them to conflicts
        {
            let mut i = 0;
            while i < self.theory_refinement_buffer.data.len() {
                if self.theory_refinement_buffer.data[i] == -1 {
                    let p = Lit(self.theory_refinement_buffer.data[i + 1]);
                    let rref = self.theory_refinement_buffer.data[i + 2] as u32;
                    if self.lit_value(p) == LBOOL_UNDEF {
                        self.unchecked_enqueue(p, CLAUSE_THEORY_REFERENCE - (rref as i32));
                    } else if self.lit_value(p) == LBOOL_FALSE {
                        let pre_len = self.theory_refinement_buffer.data.len();
                        self.theory
                            .explain(p, rref, &mut self.theory_refinement_buffer);
                        assert!(
                            self.theory_refinement_buffer.data.len() > pre_len
                                && self.theory_refinement_buffer.data[pre_len] != -1
                        ); // must have added a clause
                    } else {
                        // lit already set, ignore
                    }
                    i += 3;
                } else {
                    let len = self.theory_refinement_buffer.data[i] as usize;
                    i += 1 + len;
                }
            }
        }

        let mut backtrack_level = self.trail_lim.len() as i32;
        let mut conflict = CLAUSE_NONE;

        // second pass: check for propagation and level to backtrack
        {
            let mut i = 0;
            while i < self.theory_refinement_buffer.data.len() {
                if self.theory_refinement_buffer.data[i] == -1 {
                    i += 3;
                } else {
                    assert!(self.theory_refinement_buffer.data[i] >= 0);
                    let len = self.theory_refinement_buffer.data[i] as usize;
                    let clause_lits =
                        &mut self.theory_refinement_buffer.data[(i + 1)..(i + 1 + len)];
                    i += 1 + len;

                    if len == 0 {
                        backtrack_level = 0;
                        conflict = CLAUSE_THEORY_UNDEF;
                    } else {
                        let assigns = &self.assigns;
                        let vardata = &self.vardata;
                        clause_lits.sort_by(|x, y| {
                            use std::cmp::Ordering;
                            let x_value = Self::assigns_lit_value(assigns, Lit(*x));
                            let y_value = Self::assigns_lit_value(assigns, Lit(*y));
                            if x_value == LBOOL_UNDEF && y_value == LBOOL_UNDEF {
                                return x.cmp(y);
                            }
                            if x_value == LBOOL_UNDEF {
                                return Ordering::Less;
                            }
                            if y_value == LBOOL_UNDEF {
                                return Ordering::Greater;
                            }
                            if x_value == y_value {
                                return vardata[Lit(*y).var().idx()]
                                    .level
                                    .cmp(&vardata[Lit(*x).var().idx()].level);
                            } else {
                                if x_value == LBOOL_TRUE {
                                    return Ordering::Less;
                                } else {
                                    return Ordering::Greater;
                                }
                            }
                        });

                        if len == 1
                            || Self::assigns_lit_value(&self.assigns, Lit(clause_lits[1]))
                                == LBOOL_FALSE
                        {
                            let level = if len == 1 {
                                0
                            } else {
                                self.vardata[Lit(clause_lits[1]).var().idx()].level
                            };

                            if Self::assigns_lit_value(&self.assigns, Lit(clause_lits[0]))
                                != LBOOL_TRUE
                                || self.vardata[Lit(clause_lits[0]).var().idx()].level > level
                            {
                                backtrack_level = backtrack_level.min(level);
                            }
                        }
                    }
                }
            }

            self.cancel_until(backtrack_level);
        }

        // third pass: attach clauses and enqueue propagations, determine conflict clause
        {
            let mut i = 0;
            while i < self.theory_refinement_buffer.data.len() {
                if self.theory_refinement_buffer.data[i] == -1 {
                    i += 3;
                } else {
                    assert!(self.theory_refinement_buffer.data[i] >= 0);
                    let len = self.theory_refinement_buffer.data[i] as usize;
                    let clause_lits =
                        &self.theory_refinement_buffer.data[(i + 1)..(i + 1 + len)];
                    i += 1 + len;

                    let mut new_cref = CLAUSE_NONE;
                    if len > 1 {
                        // attach
                        new_cref = self.clause_database.add_clause(
                            unsafe {
                            std::mem::transmute::<&[i32],&[Lit]>(clause_lits)
                            }, true);
                        self.learnts.push(new_cref);
                        self.attach_clause(new_cref);
                    }

                    let first = Lit(self.theory_refinement_buffer.data[i+2]);
                    let second = Lit(self.theory_refinement_buffer.data[i+3]);
                    if conflict == CLAUSE_NONE && Self::assigns_lit_value(&self.assigns, first) != LBOOL_TRUE {
                        if len == 1
                            || (Self::assigns_lit_value(&self.assigns, second)
                                == LBOOL_FALSE && self.vardata[second.var().idx()].level <= backtrack_level) {

                                if Self::assigns_lit_value(&self.assigns, first) == LBOOL_FALSE {

                                    if len > 1 {
                                        conflict = new_cref;
                                    } else {
                                        conflict = CLAUSE_THEORY_UNDEF;
                                    }

                                } else {
                                    self.unchecked_enqueue(first, new_cref);
                                }
                        }
                    }
                }
            }

            conflict
        }
    }

    fn search(&mut self, nof_conflicts: i32) -> LBool {
        debug!("-> SEARCH(nof_conflicts={})", nof_conflicts);
        assert!(self.ok);
        let mut conflict_c = 0;
        let mut learnt_clause = Vec::new();
        self.stats.starts += 1;

        loop {
            let conflict_clause = self.propagate();
            //assert!( self.lemmas.len() == 0 ); // ?
            if conflict_clause != CLAUSE_NONE {
                trace!("found conflict");
                // found conflict
                self.stats.conflicts += 1;
                conflict_c += 1;
                if self.trail_lim.len() == 0 {
                    return LBOOL_FALSE;
                }

                learnt_clause.clear();
                trace!("Conflict in {}", conflict_clause);

                let backtrack_level = self.analyze(conflict_clause, &mut learnt_clause);

                write!(self.tracelog_file.as_mut().unwrap(), "a2").unwrap();
                for x in &learnt_clause {
                    write!(self.tracelog_file.as_mut().unwrap(), " {} ", x.0).unwrap();
                }
                write!(self.tracelog_file.as_mut().unwrap(), "\n").unwrap();

                trace!("learnt {:?}", (&backtrack_level, &learnt_clause));
                trace!("Backtrack to {}", backtrack_level);
                write!(
                    self.tracelog_file.as_mut().unwrap(),
                    "backtrack_level {}\n",
                    backtrack_level
                )
                .unwrap();
                trace!("LEARNT {:?}", learnt_clause);
                self.cancel_until(backtrack_level);

                debug!("Adding learnt");
                trace!("LEARNT {:?}", learnt_clause);
                if learnt_clause.len() == 1 {
                    self.unchecked_enqueue(learnt_clause[0], CLAUSE_NONE);
                } else {
                    let new_cref = self.clause_database.add_clause(&learnt_clause, true);
                    self.learnts.push(new_cref);
                    self.attach_clause(new_cref);
                    self.clause_bump_activity(new_cref);
                    self.unchecked_enqueue(learnt_clause[0], new_cref);
                }

                self.var_decay_activity();
                self.clause_decay_activity();

                self.learntsize_adjust_cnt -= 1;
                if self.learntsize_adjust_cnt == 0 {
                    self.learntsize_adjust_confl *= self.params.learntsize_adjust_inc;
                    self.learntsize_adjust_cnt = self.learntsize_adjust_confl as i32;
                    self.max_learnts *= self.params.learntsize_inc;

                    info!(
                        " > cfl{:>9} | vars {:>6} clauses {:>7} lits {:>6}",
                        self.stats.conflicts,
                        (self.stats.dec_vars as isize)
                            - if self.trail_lim.len() == 0 {
                                self.trail.len() as isize
                            } else {
                                self.trail_lim[0] as isize
                            },
                        self.clauses.len(),
                        self.stats.clauses_literals,
                    );
                    info!(
                        " -> learnt lim {:>8} clauses {:>8} lit/cl {:>8}",
                        self.max_learnts as isize,
                        self.learnts.len(),
                        (self.stats.learnts_literals as f64 / self.learnts.len() as f64) as isize
                    );
                }
            } else {
                // no conflict found
                trace!("no conflict found");

                if nof_conflicts >= 0 && conflict_c >= nof_conflicts || !self.within_budget() {
                    // budget cancel
                    trace!("budget cancel");
                    self.cancel_until(0);
                    return LBOOL_UNDEF;
                }

                // simplify problem clauses
                trace!("simplify?");
                if self.trail_lim.len() == 0 && !self.simplify() {
                    trace!("simplify failed");
                    return LBOOL_FALSE;
                }
                trace!("simplify ok");

                // reduce the set of learnt clauses
                trace!(
                    "learnts: {}, trail len: {}",
                    self.learnts.len(),
                    self.trail.len()
                );
                trace!("max learnts: {}", self.max_learnts);
                if self.learnts.len() as f64 - self.trail.len() as f64 >= self.max_learnts {
                    trace!("reduce_db");
                    self.reduce_db();
                }

                let mut next = LIT_UNDEF;
                while self.trail_lim.len() < self.assumptions.len() {
                    trace!("add assumption");
                    // perform user provided assumption
                    let p = self.assumptions[self.trail_lim.len()];
                    // already satisfied?
                    if self.lit_value(p) == LBOOL_TRUE {
                        // dummy decision level
                        self.trail_lim.push(self.trail.len() as i32);
                    } else if self.lit_value(p) == LBOOL_FALSE {
                        self.analyze_final(p.inverse());
                        return LBOOL_FALSE;
                    } else {
                        next = p;
                        break;
                    }
                }

                if next == LIT_UNDEF {
                    self.stats.decisions += 1;
                    next = self.pick_branch_lit();
                    trace!("pick branch lit: {:?}", next);
                    if next == LIT_UNDEF {
                        // model found
                        return LBOOL_TRUE;
                    }
                }

                // create decision level
                trace!("decision: {:?}", next);
                self.trail_lim.push(self.trail.len() as i32);
                self.theory.new_decision_level();
                self.unchecked_enqueue(next, CLAUSE_NONE);
            }
        }
    }

    fn within_budget(&self) -> bool {
        !self.asynch_interrupt
            && (self.conflict_budget < 0 || (self.stats.conflicts as i64) < self.conflict_budget)
            && (self.propagation_budget < 0
                || (self.stats.propagations as i64) < self.propagation_budget)
    }

    fn luby(y: f64, mut x: i32) -> f64 {
        let mut size = 1;
        let mut seq = 0;
        while size < x + 1 {
            seq += 1;
            size = 2 * size + 1;
        }

        while size - 1 != x {
            size = (size - 1) >> 1;
            seq -= 1;
            x = x % size;
        }

        return y.powf(seq as f64);
    }

    pub fn solve(&mut self) -> LBool {
        debug!("-> SOLVE");
        self.model.clear();
        self.conflict.clear();
        if !self.ok {
            trace!("solve: already unsat");
            return LBOOL_FALSE;
        }

        self.stats.solves += 1;

        self.max_learnts = ((self.clauses.len() as f64) * self.params.learntsize_factor)
            .max(self.params.min_learnts_lim as f64);

        self.learntsize_adjust_confl = self.params.learntsize_adjust_start_confl as f64;
        self.learntsize_adjust_cnt = self.learntsize_adjust_confl as i32;
        let mut status = LBOOL_UNDEF;

        if self.verbosity >= 1 {
            info!("* search statistics");
        }

        let mut curr_restarts = 0;
        while status == LBOOL_UNDEF {
            let rest_base = if self.params.luby_restart {
                Self::luby(self.params.restart_inc, curr_restarts)
            } else {
                self.params.restart_inc.powf(curr_restarts as f64)
            };

            status = self.search((rest_base * self.params.restart_first as f64) as i32);
            if !self.within_budget() {
                break;
            }
            curr_restarts += 1;
        }

        if self.verbosity >= 1 {
            info!("* solve finished");
        }

        if status == LBOOL_TRUE {
            self.model.resize(self.next_var as usize, LBOOL_UNDEF);
            for v in (0..self.next_var).map(|i| Var(i)) {
                self.model[v.idx()] = self.var_value(v);
            }
        } else if status == LBOOL_FALSE && self.conflict.len() == 0 {
            self.ok = false;
        }

        self.cancel_until(0);
        debug!("<- SOLVE");
        status
    }

    pub fn stats_info(&self, solve_start: cpu_time::ProcessTime) {
        let duration = cpu_time::ProcessTime::now()
            .duration_since(solve_start)
            .as_millis() as f64
            / 1000.0;
        info!("* stats:");
        info!("  - restarts: {}", self.stats.starts);
        info!(
            "  - conflicts: {}  ({:.0} /sec)",
            self.stats.conflicts,
            self.stats.conflicts as f64 / duration
        );
        info!(
            "  - decisions: {}  ({:.2}% random)  ({:.0} /sec)",
            self.stats.decisions,
            self.stats.rnd_decisions as f64 * 100.0 / self.stats.decisions as f64,
            self.stats.decisions as f64 / duration
        );
        info!(
            "  - propagations: {}  ({:.0} /sec)",
            self.stats.propagations,
            self.stats.propagations as f64 / duration
        );
        info!(
            "  - conflict literals: {}  ({:.2} % deleted)",
            self.stats.tot_literals,
            (self.stats.max_literals as f64 - self.stats.tot_literals as f64) * 100.0
                / self.stats.max_literals as f64
        );
        info!("  - cpu time: {:.2}s", duration);
    }
}

fn var_map_insert<T: Default + Clone>(map: &mut Vec<T>, Var(idx): Var, value: T, default: T) {
    map_insert(map, idx as usize, value, default)
}

fn map_insert<T: Default + Clone>(map: &mut Vec<T>, idx: usize, value: T, default: T) {
    map.resize((idx as usize + 1).max(map.len()), default);
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
