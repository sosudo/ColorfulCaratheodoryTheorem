import Mathlib
import Architect

namespace ColorfulCaratheodoryTheorem

noncomputable section

open scoped InnerProductSpace

/-- A convex hull containing zero has a point below any nonzero projection level. The proof uses convexity of the opposite halfspace. -/
@[blueprint "ColorfulCaratheodoryTheorem.MainTheorem.exists_inner_lt"]
lemma exists_inner_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (hC : (0 : E) ∈ convexHull ℝ C) (v : E) (hv : v ≠ 0) :
    ∃ x ∈ C, ⟪v, x⟫_ℝ < ‖v‖ ^ 2 := by
  by_contra! h
  have hc : Convex ℝ {x : E | ‖v‖ ^ 2 ≤ ⟪v, x⟫_ℝ} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at *
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    nlinarith
  have hz : (0 : E) ∈ {x : E | ‖v‖ ^ 2 ≤ ⟪v, x⟫_ℝ} :=
    (convexHull_min h hc) hC
  simp only [Set.mem_setOf_eq, inner_zero_right] at hz
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

/-- A point below the projection level gives a point of strictly smaller norm in a convex set. This follows from the variational characterization of a closest point. -/
@[blueprint "ColorfulCaratheodoryTheorem.MainTheorem.exists_norm_lt_of_inner_lt"]
lemma exists_norm_lt_of_inner_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hK : Convex ℝ K) (v x : E) (hv : v ∈ K) (hx : x ∈ K)
    (hlt : ⟪v, x⟫_ℝ < ‖v‖ ^ 2) : ∃ z ∈ K, ‖z‖ < ‖v‖ := by
  by_contra! h
  letI : Nonempty K := ⟨⟨v, hv⟩⟩
  have heq : ‖(0 : E) - v‖ = ⨅ w : K, ‖(0 : E) - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      simpa using h w w.property
    · have hb : BddBelow (Set.range fun w : K => ‖(0 : E) - w‖) :=
        ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
      exact ciInf_le hb ⟨v, hv⟩
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hK hv).mp heq x hx
  simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hi
  linarith

open scoped BigOperators

/-- A positive weighted average of nonnegative deviations vanishes only when each deviation vanishes. -/
@[blueprint "ColorfulCaratheodoryTheorem.MainTheorem.weighted_equal"]
lemma weighted_equal {ι : Type*} [Fintype ι] (w a : ι → ℝ) (c : ℝ)
    (hw : ∀ i, 0 < w i) (ha : ∀ i, c ≤ a i)
    (hs : ∑ i, w i * (a i - c) = 0) : ∀ i, a i = c := by
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i * (a i - c) := by
    intro i _
    exact mul_nonneg (le_of_lt (hw i)) (sub_nonneg.mpr (ha i))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hs
  intro i
  have h := hz i (Finset.mem_univ i)
  have : a i - c = 0 := (mul_eq_zero.mp h).resolve_left (ne_of_gt (hw i))
  linarith

open scoped InnerProductSpace
/-- A positive convex decomposition of a closest point lies in its supporting hyperplane. Apply the weighted nonnegative-deviation lemma. -/
@[blueprint "ColorfulCaratheodoryTheorem.MainTheorem.weighted_hyper"]
lemma weighted_hyper {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : ι → E) (w : ι → ℝ) (v : E) (hw : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = 1) (hv : (∑ i, w i • p i) = v)
    (ha : ∀ i, ‖v‖ ^ 2 ≤ ⟪v, p i⟫_ℝ) : ∀ i, ⟪v, p i⟫_ℝ = ‖v‖ ^ 2 := by
  apply weighted_equal w (fun i => ⟪v, p i⟫_ℝ) (‖v‖ ^ 2) hw ha
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  have h := congrArg (fun x => ⟪v, x⟫_ℝ) hv
  simp only [inner_sum, inner_smul_right, real_inner_self_eq_norm_sq] at h
  linarith
open scoped InnerProductSpace

/-- An affinely independent family on a nonzero supporting hyperplane cannot occupy all colors. Otherwise its affine span is the whole space. -/
@[blueprint "ColorfulCaratheodoryTheorem.MainTheorem.exists_missing_color"]
lemma exists_missing_color {ι : Type*} [Fintype ι] (d : ℕ)
    (z : ι → EuclideanSpace ℝ (Fin d)) (f : ι → Fin (d+1))
    (hf : Function.Injective f) (hz : AffineIndependent ℝ z)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0)
    (hp : ∀ i, ⟪v, z i⟫_ℝ = ‖v‖ ^ 2) : ∃ j, j ∉ Set.range f := by
  classical
  by_contra! hn
  have hs : Function.Surjective f := fun j => hn j
  have hc : Fintype.card ι = d + 1 := by
    simpa using Fintype.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)
  have ht : affineSpan ℝ (Set.range z) = ⊤ :=
    (hz.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by simpa using hc)
  have hzero : (0 : EuclideanSpace ℝ (Fin d)) ∈ affineSpan ℝ (Set.range z) := by rw [ht]; trivial
  have h : ⟪v, (0 : EuclideanSpace ℝ (Fin d))⟫_ℝ = ‖v‖ ^ 2 := by
    refine affineSpan_induction hzero ?_ ?_
    · rintro x ⟨i, rfl⟩; exact hp i
    · intro c x y z hx hy hz
      simp only [vsub_eq_sub, vadd_eq_add, inner_add_right, inner_smul_right, inner_sub_right, hx, hy, hz]
      ring
  simp only [inner_zero_right] at h
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

open scoped BigOperators
/-- A nonzero minimizer admits a convex representation omitting one color. Use a positive affinely independent representation and the supporting hyperplane. -/
@[blueprint "ColorfulCaratheodoryTheorem.MainTheorem.exists_missing_support"]
lemma exists_missing_support (d : ℕ) (p : Fin (d+1) → EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0)
    (hm : v ∈ convexHull ℝ (Set.range p))
    (hp : ∀ i, ‖v‖^2 ≤ ⟪v, p i⟫_ℝ) :
    ∃ j, v ∈ convexHull ℝ (p '' {i | i ≠ j}) := by
  classical
  obtain ⟨ι, inst, z, w, hsub, hind, hw, hsum, hvsum⟩ := eq_pos_convex_span_of_mem_convexHull hm
  letI := inst
  have he : ∀ i, ∃ j, p j = z i := fun i => hsub ⟨i, rfl⟩
  choose f hf using he
  have hfi : Function.Injective f := by
    intro a b hab
    apply hind.injective
    rw [← hf a, ← hf b, hab]
  have hhz : ∀ i, ⟪v, z i⟫_ℝ = ‖v‖^2 := by
    apply weighted_hyper z w v hw hsum hvsum
    intro i
    rw [← hf i]
    exact hp (f i)
  obtain ⟨j, hj⟩ := exists_missing_color d z f hfi hind v hv hhz
  refine ⟨j, ?_⟩
  rw [← hvsum]
  apply (convex_convexHull ℝ _).sum_mem (t := Finset.univ) (w := w)
  · intro i _; exact le_of_lt (hw i)
  · exact hsum
  · intro i _
    apply subset_convexHull ℝ _
    refine ⟨f i, ?_, hf i⟩
    intro heq
    apply hj
    exact ⟨i, heq⟩

/-- A global minimum-norm point among colorful convex hulls is zero. Replace a missing color by a point that strictly decreases its norm. -/
@[blueprint "ColorfulCaratheodoryTheorem.MainTheorem.minimal_colorful_zero"]
lemma minimal_colorful_zero (d : ℕ)
    (C : Fin (d+1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i))
    (p : Fin (d+1) → EuclideanSpace ℝ (Fin d)) (hp : ∀ i, p i ∈ C i)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ convexHull ℝ (Set.range p))
    (hmin : ∀ q, (∀ i, q i ∈ C i) → ∀ z ∈ convexHull ℝ (Set.range q), ‖v‖ ≤ ‖z‖) : v = 0 := by
  classical
  by_contra hn
  have hh : ∀ i, ‖v‖ ^ 2 ≤ ⟪v, p i⟫_ℝ := by
    intro i
    by_contra! hlt
    obtain ⟨y, hy, hylt⟩ := exists_norm_lt_of_inner_lt _ (convex_convexHull ℝ _) v (p i) hv
      (subset_convexHull ℝ _ ⟨i, rfl⟩) hlt
    exact (not_lt_of_ge (hmin p hp y hy)) hylt
  obtain ⟨j, hj⟩ := exists_missing_support d p v hn hv hh
  obtain ⟨x, hx, hlt⟩ := exists_inner_lt (C j) (hC j) v hn
  let q := Function.update p j x
  have hq : ∀ i, q i ∈ C i := by
    intro i
    by_cases h : i = j
    · subst i; simpa [q] using hx
    · simpa [q, h, Ne.symm h] using hp i
  have hsub : p '' {i | i ≠ j} ⊆ Set.range q := by
    rintro _ ⟨i, hi, rfl⟩
    have hne : i ≠ j := hi
    exact ⟨i, by simp [q, hne]⟩
  have hvq : v ∈ convexHull ℝ (Set.range q) := convexHull_mono hsub hj
  have hxq : x ∈ convexHull ℝ (Set.range q) := subset_convexHull ℝ _ ⟨j, by simp [q]⟩
  obtain ⟨y, hy, hylt⟩ := exists_norm_lt_of_inner_lt _ (convex_convexHull ℝ _) v x hvq hxq hlt
  exact (not_lt_of_ge (hmin q hq y hy)) hylt


/-- Finite color classes admit a globally minimum-norm point in a colorful hull. The finite union of compact convex hulls is compact. -/
@[blueprint "ColorfulCaratheodoryTheorem.MainTheorem.exists_colorful_min"]
lemma exists_colorful_min (d : ℕ) (C : Fin (d+1) → Finset (EuclideanSpace ℝ (Fin d)))
    (hne : ∀ i, (C i).Nonempty) :
    ∃ (p : Fin (d+1) → EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin d)),
    (∀ i, p i ∈ C i) ∧ v ∈ convexHull ℝ (Set.range p) ∧
    (∀ q, (∀ i, q i ∈ C i) → ∀ y ∈ convexHull ℝ (Set.range q), ‖v‖ ≤ ‖y‖) := by
  classical
  let P : Set (Fin (d+1) → EuclideanSpace ℝ (Fin d)) := {p | ∀ i, p i ∈ C i}
  have hP : P.Finite := Set.Finite.pi' (fun i => (C i).finite_toSet)
  let K : Set (EuclideanSpace ℝ (Fin d)) := ⋃ p ∈ P, convexHull ℝ (Set.range p)
  have hK : IsCompact K := hP.isCompact_biUnion (by
    intro p hp
    exact (Set.finite_range p).isCompact_convexHull)
  have hKn : K.Nonempty := by
    choose p hp using hne
    have : p ∈ P := hp
    exact ⟨p 0, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨this,
      subset_convexHull ℝ _ ⟨0, rfl⟩⟩⟩⟩
  obtain ⟨v, hvK, hvmin⟩ := hK.exists_isMinOn hKn continuous_norm.continuousOn
  obtain ⟨p, hp, hv⟩ := Set.mem_iUnion₂.mp hvK
  refine ⟨p, v, hp, hv, ?_⟩
  intro q hq y hy
  apply hvmin
  exact Set.mem_iUnion₂.mpr ⟨q, hq, hy⟩

/-- The colorful Carathéodory theorem (statement): if each of `d+1` sets of points in `ℝ^d`
contains the origin in its convex hull, then one can pick one point from each set so that the
origin lies in the convex hull of the chosen points. Reduce to finite sets and choose a
minimum-norm point among colorful convex hulls; the replacement argument forces it to be zero. -/
@[blueprint "ColorfulCaratheodoryTheorem.MainTheorem"]
theorem MainTheorem (d : ℕ)
    (C : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i)) :
    ∃ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i, p i ∈ C i) ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range p) := by
  classical
  let S := fun i => Caratheodory.minCardFinsetOfMemConvexHull (hC i)
  have hS : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (S i : Set _) :=
    fun i => Caratheodory.mem_minCardFinsetOfMemConvexHull (hC i)
  have hne : ∀ i, (S i).Nonempty := fun i => Caratheodory.minCardFinsetOfMemConvexHull_nonempty (hC i)
  obtain ⟨p, v, hp, hv, hmin⟩ := exists_colorful_min d S hne
  have hz : v = 0 := minimal_colorful_zero d (fun i => (S i : Set _)) hS p hp v hv hmin
  refine ⟨p, ?_, hz ▸ hv⟩
  intro i
  exact Caratheodory.minCardFinsetOfMemConvexHull_subseteq (hC i) (hp i)

end

end ColorfulCaratheodoryTheorem

