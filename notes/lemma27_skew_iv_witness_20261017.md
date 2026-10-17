# Last-branch witness proof under b>0, q>0, m+q>1

This closes a distinct obstacle, the actual special skew witness
clause IV, without appealing to a full skewB/completeB theorem
for the joined final support.

The exact final support has a root (verified), all final ranks <M,
complete directional branching below rank M-1, and no successors
at rank M-1. The verified final condIII strictly separates the
ambient lengths of earlier/later intrinsic support ranks.
For M>1 and b>0, the root has an immediate successor, so
the interior list is nonempty.

A standalone generic finite linear-order lemma selects a
maximal interior star under the repaired length-first forward
auxiliary order. Every vertex strictly after star must be a
leaf by maximality. Every vertex strictly before star has
final rank <M-1: otherwise condIII would make its ambient
length strictly larger than star, contradicting the
forward-length order. Hence every such earlier vertex is
fully b-branching, and star itself is fully b-branching.
The generic LastBranchWitness lemma with maximal direction
b-1 establishes actual SkewTree.condIVB.

The M=1 singleton case is intentionally not asserted to have
a condIVB witness: SkewTree.skewB includes singleton supports
by explicit convention. The next global proof must split M=1
from M>1 before combining rootedness, condIIB, condIIIB and IV.

The printed reverse-starred interface and final f' remain separate.
