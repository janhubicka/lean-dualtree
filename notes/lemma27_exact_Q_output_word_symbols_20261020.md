# Exact equality of dependent output word symbols (not Q objects)

The corrected actual fibrewise Q has now been decomposed exhaustively.

* Early original ambient f roots are fixed by complete signature.
* Safe late original f roots are P_i(z); chosen finite auxiliary
  letters decode exactly to the requested O symbol there.
* At an unsafe late f root, the actual Q sampler uses its
  original fallback. The crucial point is a selected frontier
  may still exist; the verified inverse-prefix/safe-reconstruction
  lemmas show its local tail must be too long, so the sampler falls
  back. PR #400 already established that O has the identical
  fallback constant under the two-letter span hypothesis.
* On whole ambient f fibres, Q is syntactically uniform and O is
  uniform by verified two-letter span inclusion, so root equality
  implies equality everywhere.

The exact dependent variable types are transported via the already
formalized SAME-complete-signature root equivalence: no implicit
identification of distinct support-subtype names.

This does NOT imply object-valued Q(w)=O: matching terminal D2
positions and the whole starred tree remains. It also DOES NOT
place the constructed local coordinate input in the Ramsey span
of the mixed product word f; ordinary letters must still be
chosen consistently along each f_i variable fibre.
