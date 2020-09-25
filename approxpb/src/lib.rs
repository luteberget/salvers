use sattrait::*;
use totalizer::*;
use ordered_float::OrderedFloat;


struct ApproxCountingParams {
    low_coeff :f64,
    rhs_max :f64,
    rounding_max :f64,
}

impl Default for ApproxCountingParams {
    fn default() -> Self {
        ApproxCountingParams {
            low_coeff: 0.2,
            rhs_max: 0.5,
            rounding_max: 0.1,
        }
    }
}

/// If the given pseudo-boolean constraint is can be efficiently approximated by an eager SAT
/// encoding, add an approximate version of the  constraint to the SAT problem. Returns true if the
/// constraint was added.
pub fn opportunistic_approximate_counting_lte_constraint<L :Lit>(problem :&mut impl SatInstance<L>, 
                                                                 mut terms :Vec<(f64, L)>,
                                                                 mut rhs: f64) -> bool {
    // Assume positive coefficients.
    if rhs < 0.0 || terms.iter().any(|(c,_)| *c < 0.0) { todo!("negative coeffs not supported."); }

    let params :ApproxCountingParams = Default::default();

    let num_components = terms.len();
    let coeff_sum = terms.iter().map(|(c,_)| *c).sum::<f64>();
    let avg_coeff = coeff_sum / num_components as f64;

    // 1. eliminate low coefficients.
    let mut dropped_value = 0.0;
    terms.retain(|(c,_)| {
           if *c < params.low_coeff * avg_coeff {
               dropped_value += *c; false
           } else { true }
        });

    // Give up if there were a large number of low coefficients.
    // (too much coeff variance for efficient SAT encoding)
    if terms.len() == 0 || dropped_value > avg_coeff { return false;}

    // 2. scale up coefficients
    let unit = terms.iter().map(|(c,_)| OrderedFloat(*c)).min().unwrap().into_inner();
    for (c,_) in terms.iter_mut() { *c /= unit; }
    rhs /= unit;

    // 3. if the rhs is too big
    if rhs > params.rhs_max * num_components as f64 { return false; }

    // 4. round rhs up to integer
    let rhs_int = unit.ceil() as u32;
    let rhs_diff = rhs_int as f64 - rhs;
    if rhs_diff / rhs > 0.2 { return false; }
    let rhs = rhs_int;

    // 5. round coefficents down to integers
    let mut round_value = 0.0;
    let int_terms = terms.into_iter().filter_map(|(c,l)| {
        if c > rhs as f64 {
            problem.add_clause([!l].iter().copied());
            None
        } else {
            let int_c = c.floor() as usize;
            round_value += c - int_c as f64;
            Some((int_c, l))
        }
    }).collect::<Vec<(usize, L)>>();

    if round_value > params.rounding_max * rhs as f64 { return false; }

    // The constraint is efficiently encodable to SAT.
    // Call the totalizer encoding.

    println!("totalizer on {} terms < {}", int_terms.iter().map(|(c,_)| *c).sum::<usize>(), rhs);
    Totalizer::count(problem,
                     int_terms.iter().flat_map(|(c,l)| std::iter::repeat(*l).take(*c)),
                     rhs);
    true
}

