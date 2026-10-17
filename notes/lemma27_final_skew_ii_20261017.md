# Final skew condition II on the corrected rank-filtered support

For every s,t in the actual finite support S,
if h_S(s)=h_S(t) and s <=lex t, then |s|<=|t|.

Retained/retained: the inherited exact T height formula and T skew II.
Retained/projected: equality forces both original T ranks to equal the
distinguished m and the local support rank to be zero. The verified
retained-first lex geometry plus original T skew length comparison applies.
Projected/retained: same equality forces old-first lex, and the
reverse orientation would identify an old and a new cut-separated node.
Projected/projected: the newly isolated full equal-final-rank theorem
covers every sorted frontier cone pair and both m/m+1 rank bands.

The statement refers to the original executable SkewTree.condIIB
on (finalBudgetSupport c f M).toList. It is not a parameterized
replacement or a conditional "assume skew" wrapper.

Together with the already merged condIIIB theorem, both numeric skew
clauses are fully discharged. Final skew clause IV, rootedness and
global completeB still require their own explicit proof, as do
construction of f' and transfer of the paper's original starred
mixed-product assumptions to the corrected forward class.
