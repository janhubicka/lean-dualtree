# Adversarial audit of early fibres and source-assignment anchoring

CAUTION: It is false in general that for EVERY assignment sigma to the
full final support T' and EVERY old source assignment tau, one has
eval(Q(x_sigma),tau) = eval(f',sigma) on early f-variable fibres.

Reason: the correct fibrewise Q uses g' = f[rho] at any early original
f-fibre, whereas the constructed ambient f' fixes ALL retained T roots,
including additional roots not in g' support. Their assignments
are independent in the full f' span, but g' at them may be fixed
or tied to another old source variable.

A mathematically justified alignment is:
- choose arbitrary old source-variable assignment tau;
- choose arbitrary base assignment sigma0 on final f' roots;
- define sigma(v) = evalSymbol(tau,rho(v)) when v is retained
  at/before the corrected forward cut; otherwise sigma0(v).

This anchored assignment agrees with the SOURCE substitution
at every early original f-root and does not alter ANY selected
projected final root P_i(z) (all are strictly after cut).
Hence the actual fibrewise corrected Q-word, evaluated under tau,
agrees with f' evaluated under sigma at EVERY early f-fibre
position. Original ambient constants match unconditionally.
Safe late projected f-fibres already match under arbitrary sigma
by the merged whole-fibre Q comparison.

The remaining f-fibres are late original T roots with NO safe
projected local address: no selected frontier or an unsafe local
tail. To obtain the global equality, first prove that such a
root is NOT in the selected final variable support, so the
global f' substitution emits the fallback constant. Then apply
the already checked ForwardQFibreDefaults facts that genuine
fibrewise Q also emits fallback on these late f-fibres.
Only AFTER these cases can one claim global evaluated Q/f'
equality for this anchored sigma. Finally the Ramsey proof
must audit the direction of the required inclusion between
colouring domains; anchoring selects a restricted subset of
the full f' span.

This proof uses the corrected forward auxiliary order and makes
NO claim about the printed reverse-starred mixed-product domain.
