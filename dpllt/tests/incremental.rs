use dpllt;

#[test]
fn basic_incremental_use() {
    use dpllt::*;

    let mut s = SatSolver::new();
    let x = s.prop.new_var(LBOOL_UNDEF, true);
    let y = s.prop.new_var(LBOOL_UNDEF, true);
    let z = s.prop.new_var(LBOOL_UNDEF, true);

    s.prop.add_clause(vec![x, y, z]);

    for negs in [
        vec![x],
        vec![y],
        vec![z],
        vec![x, y],
        vec![x, z],
        vec![y, z],
    ]
    .iter()
    {
        println!("solving {:?} v {:?} v {:?}  and neg {:?}", x, y, z, negs);
        s.prop.set_assumptions(negs.iter().map(|l| l.inverse()));
        assert!(s.prop.solve() == LBOOL_TRUE);
        let model = s
            .prop
            .get_model()
            .unwrap()
            .iter()
            .map(|l| *l == LBOOL_TRUE)
            .collect::<Vec<bool>>();
        println!("model: {:?}", model);
        assert!(model[x.var().idx()] || model[y.var().idx()] || model[z.var().idx()]);
        for n in negs.iter() {
            assert!(model[n.var().idx()] == false);
        }
    }

    println!("checking !x,!y,!z is unsat.");
    s.prop
        .set_assumptions(vec![x, y, z].iter().map(|l| l.inverse()));
    assert!(s.prop.solve() == LBOOL_FALSE);
}
