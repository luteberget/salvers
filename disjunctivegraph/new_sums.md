# old algorithm
We have some sum constraints
  xi1 + xi2 + ... xin <= c (marker lit y)
When they are violated by m decisions with cost ci, we get.
  d1 ^ d2 ^ ... ^ dm => !y
if y is then part of a MUS we use the smallest cost cmin (out of the ci's) and add:
  xi1 + xi2 + ... + xin <= cmin
and a new constraint combining the sum of all clauses

# new algorithm
We have a sum constraint
  xi1 + ... + xin <= c (marker lit y)
When this is violated by m decisions {di} with cost ci, we add:
  new lit "xi1 + ... + xin >= ci"
  d1 ^ ... ^ dm => "xi1 + ... + xin >= ci"
  ..and possibly "xi1 + ... + xin >= ci" => !"xi1 + ... + xin <= c"

then y is part of a MUS. we relax the sum constraint by adding cmin.
then we create a new sum constraint with all individual sums
  xj1 + ... + xjl <= sum(c) + cmin
and we look through all known violations to the individual sums and find
the "pareto front" (?) of known constraints.


