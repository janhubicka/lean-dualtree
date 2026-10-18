# Corrected Lemma 27: ambient bounded root lift, 18 October 2026

The corrected final complete-skew support S is a Finset(Node b) included
in the original ambient complete support T. A FibreFrame records a
VariableWord f whose roots are EXACTLY T, with T bounded by ambient n.

This module:
1. lifts S without loss/duplication to a bounded-root Finset and list,
2. proves that the lifted roots are all actual original f roots,
3. exhibits the original T root in S, prefixing every original f root,
4. applies root-compatible substitution to construct a legal
   **coarse** VariableWord with exactly S as its support,
5. proves its evaluated span is contained in span(f).

The construction uses no capacity, Hall matching, or unseen alphabet
assumption, and does not invent any variable roots.

ADVERSARIAL LIMITATION: The coarse collapse sends all deleted original
variables to the ambient root. In general this does NOT agree with the
mixed-product local variable words f_i on their fibres; it is NOT the
final f' asserted by Lemma 27. It is only a useful structural bridge.
The full proof must construct rho from the local cone words,
prove it is root-compatible, show the resulting word agrees with
the Q image in all relevant positions, and then apply its span
containment. Original starred reverse-order hypotheses must still
be reconciled with the corrected forward Frame.
