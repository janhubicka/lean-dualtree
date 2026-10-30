import DualTree.FlatHalesJewett
import DualTree.KVariableWord

/-!
# A genuinely root-aligned height-one tree Ramsey line

The flat Hales–Jewett theorem gives a nonempty variable set on a
linear collection of word slots. To make this a LEGAL tree variable
word, put the slots along one fixed ray of the b-ary tree and root
the variable at its FIRST occurrence. The variable then occurs
only above its root. A singleton variable-root support is
1-complete skew, for either auxiliary order.

This proves a positive existence theorem for one-variable
KVariableWord b n 1 over a sufficiently tall homogeneous tree,
not merely a flat SpanAudit word.

It does NOT yet build a k-complete skew support when k>1,
a vector-complete skew family, a mixed D₁/D₂ word or a
quantitative mixed c-good Ramsey witness.
-/

namespace DualTree.RayHalesJewett

/-- The all-zero ray in a nonempty b-ary tree. -/
def zeroRay {b : Nat} (hb : 0 < b) (j : Nat) : Node b :=
  List.replicate j ⟨0, hb⟩

/-- A monotone branch prefix: earlier ray positions are ancestors. -/
theorem zeroRay_prefix {b : Nat} (hb : 0 < b)
    (i j : Nat) (h : i ≤ j) :
    IsPrefix (zeroRay hb i) (zeroRay hb j) := by
  refine ⟨zeroRay hb (j - i), ?_⟩
  change zeroRay hb j = zeroRay hb i ++ zeroRay hb (j - i)
  have hj : j = i + (j - i) := by omega
  calc
    zeroRay hb j = zeroRay hb (i + (j - i)) :=
      congrArg (zeroRay hb) hj
    _ = zeroRay hb i ++ zeroRay hb (j - i) := by
      simp only [zeroRay, List.replicate_add]

/-- The N flat word slots, at distinct consecutive levels
0, ..., N-1 on one ray inside b^{<N+1}. -/
def rayPos {b N : Nat} (hb : 0 < b) (j : Fin N) :
    BoundedNode b (N + 1) :=
  ⟨zeroRay hb j.val, by
    simp [InHomTree, zeroRay]⟩

/-- Recognize exactly the N ray positions, and recover their
finite coordinate index. The extra top level N remains fixed. -/
noncomputable def rayIndex {b N : Nat} (hb : 0 < b)
    (t : BoundedNode b (N + 1)) : Option (Fin N) :=
  if h : t.1 = zeroRay hb t.1.length ∧ t.1.length < N then
    some ⟨t.1.length, h.2⟩
  else none

theorem rayIndex_rayPos {b N : Nat} (hb : 0 < b)
    (j : Fin N) :
    rayIndex hb (rayPos hb j) = some j := by
  simp [rayIndex, rayPos, zeroRay]

theorem rayIndex_some {b N : Nat} (hb : 0 < b)
    (t : BoundedNode b (N + 1)) (j : Fin N)
    (h : rayIndex hb t = some j) :
    t = rayPos hb j := by
  unfold rayIndex at h
  split_ifs at h with ht
  · have hidx : (⟨t.1.length, ht.2⟩ : Fin N) = j :=
      Option.some.inj h
    have hl : t.1.length = j.val :=
      congrArg Fin.val hidx
    apply Subtype.ext
    change t.1 = zeroRay hb j.val
    calc
      t.1 = zeroRay hb t.1.length := ht.1
      _ = zeroRay hb j.val := by rw [hl]

/-- A root name for the singleton support at ray position r. -/
def rootVar {b N : Nat} (hb : 0 < b) (r : Fin N) :
    {t : BoundedNode b (N + 1) // t ∈ [rayPos hb r]} :=
  ⟨rayPos hb r, by simp⟩

/-- Lift a FLAT one-variable word to a tree word. Every variable
occurrence uses the singleton genuine root variable name. The
word is constant outside the N designated ray positions. -/
noncomputable def raySymbol {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1))
    (fallback : β)
    (r : Fin N)
    (t : BoundedNode b (N + 1)) :
    Sum β {u : BoundedNode b (N + 1) // u ∈ [rayPos hb r]} :=
  match rayIndex hb t with
  | none => Sum.inl fallback
  | some j =>
      match w j with
      | Sum.inl a => Sum.inl a
      | Sum.inr _ => Sum.inr (rootVar hb r)

/-- The selected ray-root is labelled by its ACTUAL variable. -/
theorem raySymbol_at_root {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0) :
    raySymbol hb w fallback r (rayPos hb r) =
      Sum.inr (rootVar hb r) := by
  simp [raySymbol, rayIndex_rayPos, hroot]

/-- Every variable occurrence is above its chosen first
occurrence. This is the exact tree-variable-word below-root
law, not a flat syntactic substitution statement. -/
theorem raySymbol_below {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hfirst : ∀ (j : Fin N) (v : Fin 1),
      w j = Sum.inr v → r ≤ j)
    (v : {u : BoundedNode b (N + 1) // u ∈ [rayPos hb r]})
    (t : BoundedNode b (N + 1))
    (hv : raySymbol hb w fallback r t = Sum.inr v) :
    IsPrefix v.1.1 t.1 := by
  cases hi : rayIndex hb t with
  | none =>
      simp [raySymbol, hi] at hv
  | some j =>
      cases hw : w j with
      | inl a =>
          simp [raySymbol, hi, hw] at hv
      | inr u =>
          have hname : rootVar hb r = v := by
            simpa [raySymbol, hi, hw] using hv
          have hpos : t = rayPos hb j :=
            rayIndex_some hb t j hi
          have hrootNode : v.1 = rayPos hb r := by
            exact congrArg Subtype.val hname.symm
          have hle : r.val ≤ j.val := hfirst j u hw
          change IsPrefix v.1.1 t.1
          rw [hrootNode, hpos]
          exact zeroRay_prefix hb r.val j.val hle

/-- Convert one proper flat Hales–Jewett line to a TRUE
tree-variable word. The root is the first variable
occurrence, so both the at-root and below-root conditions
are verified. -/
noncomputable def rayVariableWord {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ (j : Fin N) (v : Fin 1),
      w j = Sum.inr v → r ≤ j) :
    VariableWord b (N + 1) β where
  support := [rayPos hb r]
  support_nodup := by simp
  word := raySymbol hb w fallback r
  atRoot := by
    intro v
    have hname : v = rootVar hb r := by
      apply Subtype.ext
      change v.1 = rayPos hb r
      simpa using v.2
    subst v
    exact raySymbol_at_root hb w fallback r hroot
  below := by
    intro v t ht
    exact raySymbol_below hb w fallback r hfirst v t ht

/-- The singleton root of the lifted Hales–Jewett line
is a 1-complete skew support in the genuine tree
geometry, not merely a proper flat word. -/
noncomputable def rayKVariableWord {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ (j : Fin N) (v : Fin 1),
      w j = Sum.inr v → r ≤ j) :
    KVariableWord b (N + 1) 1 β
      (SkewTree.forwardAuxB (b := b)) where
  toVariableWord := rayVariableWord hb w fallback r hroot hfirst
  complete_support := by
    change SkewTree.completeB SkewTree.forwardAuxB 1
      [zeroRay hb r.val] = true
    exact SkewTree.singleton_complete_oneB _ _

/-- Embed a flat word into the entire homogeneous tree by
reading the N ray slots and fixing every other node. This
embedding is independent of the later Hales–Jewett word. -/
noncomputable def embedRay {b N : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin N → β) : TreeWord b (N + 1) β :=
  fun t =>
    match rayIndex hb t with
    | none => fallback
    | some j => u j

/-- Every genuine tree-word evaluation of the lifted
one-variable word is EXACTLY the embedding of the original
flat evaluation. This proves the transfer of the entire
monochromatic Hales–Jewett line, not just one assignment. -/
theorem rayVariableWord_eval {b N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ (j : Fin N) (v : Fin 1),
      w j = Sum.inr v → r ≤ j)
    (σ : (rayVariableWord hb w fallback r hroot hfirst).Vars → β) :
    (rayVariableWord hb w fallback r hroot hfirst).eval σ =
      embedRay hb fallback
        (SpanAudit.eval w (fun _ => σ (rootVar hb r))) := by
  funext t
  change SpanAudit.eval (raySymbol hb w fallback r) σ t =
    embedRay hb fallback
      (SpanAudit.eval w (fun _ => σ (rootVar hb r))) t
  cases hi : rayIndex hb t with
  | none =>
      simp [raySymbol, embedRay, SpanAudit.eval,
        SpanAudit.evalSymbol, hi]
  | some j =>
      cases hw : w j with
      | inl a =>
          simp [raySymbol, embedRay, SpanAudit.eval,
            SpanAudit.evalSymbol, hi, hw]
      | inr v =>
          simp [raySymbol, embedRay, SpanAudit.eval,
            SpanAudit.evalSymbol, hi, hw]

/-- Every proper flat one-variable word has a genuine
FIRST variable occurrence in its finite ordered index set. -/
theorem exists_first_variable_index
    {N : Nat} {β : Type*}
    (w : Fin N → Sum β (Fin 1))
    (hproper : ∀ v : Fin 1, ∃ j : Fin N, w j = Sum.inr v) :
    ∃ r : Fin N, w r = Sum.inr 0 ∧
      (∀ (j : Fin N) (v : Fin 1),
        w j = Sum.inr v → r ≤ j) := by
  classical
  let S : Finset (Fin N) :=
    Finset.univ.filter (fun j => ∃ v : Fin 1, w j = Sum.inr v)
  have hnon : S.Nonempty := by
    obtain ⟨j,hj⟩ := hproper 0
    refine ⟨j, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨0,hj⟩⟩
  let r := S.min' hnon
  have hrmem : r ∈ S := Finset.min'_mem S hnon
  obtain ⟨v,hv⟩ := (Finset.mem_filter.mp hrmem).2
  have hvzero : v = 0 := Fin.eq_zero v
  refine ⟨r, by simpa [hvzero] using hv, ?_⟩
  intro j v hj
  have hjmem : j ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨v,hj⟩⟩
  exact Finset.min'_le S j hjmem

/-- The first genuine tree-compatible finite Hales–Jewett
existence statement: one can ALWAYS find a sufficiently
tall homogeneous tree and a 1-complete skew variable word
whose whole evaluated tree-word span is monochromatic.

This works for arbitrary finite alphabet and colour type
and all nonempty branching factors b; a fallback letter
specifies the colouring-independent values off the ray.
The variable root is NOT assumed in advance, avoiding
the false assertion that an arbitrary colouring admits
a line through a predetermined fixed root. -/
theorem exists_monochromatic_one_root_tree_word
    {b : Nat} (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β) :
    ∃ n : Nat, ∀ c : TreeWord b n β → γ,
      ∃ f : KVariableWord b n 1 β
          (SkewTree.forwardAuxB (b := b)),
        ∃ col : γ, ∀ u : TreeWord b n β,
          u ∈ f.span → c u = col := by
  obtain ⟨N,hN⟩ :=
    FlatHalesJewett.exists_monochromatic_flat_word β γ 1
  refine ⟨N + 1, ?_⟩
  intro c
  let C : (Fin N → β) → γ :=
    fun u => c (embedRay hb fallback u)
  obtain ⟨w,hproper,col,hmono⟩ := hN C
  obtain ⟨r,hroot,hfirst⟩ :=
    exists_first_variable_index w hproper
  let f := rayKVariableWord hb w fallback r hroot hfirst
  refine ⟨f, col, ?_⟩
  intro u hu
  obtain ⟨σ,hσ⟩ := hu
  have heval := rayVariableWord_eval
    hb w fallback r hroot hfirst σ
  have hc := hmono (fun _ => σ (rootVar hb r))
  calc
    c u = c (f.toVariableWord.eval σ) := by
      exact congrArg c hσ.symm
    _ = C (SpanAudit.eval w (fun _ => σ (rootVar hb r))) := by
      exact congrArg c heval
    _ = col := hc

end DualTree.RayHalesJewett
