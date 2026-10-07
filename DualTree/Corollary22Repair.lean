import Mathlib

/-!
# The two-root bridge behind the Corollary 22 repair

After Theorem 13 has produced a c-good subspace, the color on a pointed
coordinate is allowed to depend only on the marked root and the letter seen at
that root.  For a Gamma1-coordinate, smoothness lets the marked root move while
the underlying word is kept fixed.

With at least two available roots, these two moves eliminate the remaining
letter dependence completely.  This is the elementary bridge missing in the
height-one case of Corollary 22.
-/

namespace DualTree.Corollary22Repair

/--
Abstract c-goodness for one pointed coordinate: at a fixed marked root, the
color depends only on the letter at that root.
-/
def Good {R A C : Type*} (c : (R → A) → R → C) : Prop :=
  ∀ a b t, a t = b t → c a t = c b t

/--
Abstract Gamma1-smoothness: for a fixed underlying assignment, moving the
marked root does not change the color.
-/
def RootSmooth {R A C : Type*} (c : (R → A) → R → C) : Prop :=
  ∀ a t u, c a t = c a u

def HasTwoRoots (R : Type*) : Prop :=
  ∃ p q : R, p ≠ q

/--
Two roots are enough to bridge arbitrary source and target letters.
-/
theorem constant_of_good_rootSmooth_twoRoots {R A C : Type*}
    (c : (R → A) → R → C)
    (hgood : Good c)
    (hsmooth : RootSmooth c)
    (hroots : HasTwoRoots R) :
    ∀ a t b u, c a t = c b u := by
  classical
  rcases hroots with ⟨p, q, hpq⟩
  intro a t b u
  let d : R → A := fun x =>
    if x = p then a p
    else if x = q then b q
    else a x
  have hdp : d p = a p := by
    simp [d]
  have hdq : d q = b q := by
    simp [d, hpq.symm]
  calc
    c a t = c a p := hsmooth a t p
    _ = c d p := hgood a d p hdp.symm
    _ = c d q := hsmooth d p q
    _ = c b q := hgood d b q hdq
    _ = c b u := hsmooth b q u

/-- Height one shows that the two-root hypothesis is genuinely needed. -/
def singletonColor (a : PUnit → Bool) (_ : PUnit) : Bool :=
  a PUnit.unit

theorem singletonColor_good : Good singletonColor := by
  intro a b t h
  cases t
  simpa [singletonColor] using h

theorem singletonColor_rootSmooth : RootSmooth singletonColor := by
  intro a t u
  cases t
  cases u
  rfl

theorem singletonColor_not_constant :
    ¬ ∀ a t b u, singletonColor a t = singletonColor b u := by
  intro h
  let a : PUnit → Bool := fun _ => false
  let b : PUnit → Bool := fun _ => true
  have hc := h a PUnit.unit b PUnit.unit
  simp [singletonColor, a, b] at hc

end DualTree.Corollary22Repair
