import Submission.Obl.k4_matching_homogeneous_records.Homogenize

/-!
# Homogenizing measurable record maps

The finite homogenization of `Homogenize.lean`, applied to the classes of the finest record
map `F q` on a measurable set `S`, weighted by the measure of each class.
-/

namespace Submission.Obl.k4_matching_homogeneous_records

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

/-- **Homogenization of measurable nested records.** One keeps a measurable part `S'` of `S`
carrying a `(Nat.log 2 #(F q '' S) + 1) ^ (-q)` part of the mass of `S`, on which every
level-`a` record has at most `2 ^ (b - a)` times the average number of level-`b` descendants. -/
theorem measure_homogenize (μ : Measure X) [IsFiniteMeasure μ] (q : ℕ) (F : ℕ → X → ℕ)
    (hFm : Measurable (F q)) (S : Set X) (hS : MeasurableSet S)
    (hfin : (F q '' S).Finite)
    (hnest : ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ S, ∀ y ∈ S, F b x = F b y → F a x = F a y) :
    ∃ S' ⊆ S, MeasurableSet S' ∧
      μ.real S ≤ ((Nat.log 2 (F q '' S).ncard + 1 : ℕ) : ℝ) ^ q * μ.real S' ∧
      (∀ a b, a ≤ b → b ≤ q → (F a '' S').ncard ≤ (F b '' S').ncard) ∧
      (∀ a b, a ≤ b → b ≤ q → ∀ x ∈ S',
        (F b '' {y | y ∈ S' ∧ F a y = F a x}).ncard * (F a '' S').ncard ≤
          2 ^ (b - a) * (F b '' S').ncard) := by
  rcases S.eq_empty_or_nonempty with hS0 | ⟨x₀, hx₀⟩
  · refine ⟨∅, by simp [hS0], MeasurableSet.empty, by simp [hS0], by simp, by simp⟩
  have : Nonempty X := ⟨x₀⟩
  set L := hfin.toFinset with hL
  let rep : ℕ → X := Function.invFunOn (F q) S
  have hrep : ∀ c ∈ L, rep c ∈ S ∧ F q (rep c) = c := by
    intro c hc
    rw [hL, Set.Finite.mem_toFinset] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact Function.invFunOn_pos ⟨x, hx, rfl⟩
  let G : ℕ → ℕ → ℕ := fun k c => F k (rep c)
  have hFq : ∀ x ∈ S, F q x ∈ L := fun x hx => by
    rw [hL, Set.Finite.mem_toFinset]; exact ⟨x, hx, rfl⟩
  have hGF : ∀ k ≤ q, ∀ x ∈ S, G k (F q x) = F k x := by
    intro k hk x hx
    obtain ⟨h1, h2⟩ := hrep (F q x) (hFq x hx)
    exact hnest k q hk le_rfl (rep (F q x)) h1 x hx h2
  have hGn : Nested G q L := by
    intro a b hab hbq c hc c' hc' h
    exact hnest a b hab hbq (rep c) (hrep c hc).1 (rep c') (hrep c' hc').1 h
  let w : ℕ → ℝ := fun c => μ.real (S ∩ F q ⁻¹' {c})
  obtain ⟨T, hTL, hmass, hmono, hdesc⟩ := finite_homogenize G q L w hGn
  set S' := S ∩ F q ⁻¹' (T : Set ℕ) with hS'
  have hS'S : S' ⊆ S := Set.inter_subset_left
  have hS'm : MeasurableSet S' := hS.inter (hFm MeasurableSet.of_discrete)
  -- the images of `S'` are images of `T`
  have himage : ∀ k ≤ q, F k '' S' = ↑(T.image (G k)) := by
    intro k hk
    ext e
    simp only [Set.mem_image, Finset.coe_image, Set.mem_inter_iff, Set.mem_preimage,
      Finset.mem_coe, hS']
    constructor
    · rintro ⟨x, ⟨hx, hxT⟩, rfl⟩
      exact ⟨F q x, hxT, hGF k hk x hx⟩
    · rintro ⟨c, hcT, rfl⟩
      obtain ⟨h1, h2⟩ := hrep c (hTL hcT)
      exact ⟨rep c, ⟨h1, by rw [h2]; exact hcT⟩, rfl⟩
  have hdimage : ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ S',
      F b '' {y | y ∈ S' ∧ F a y = F a x} =
        ↑((T.filter (fun c => G a c = G a (F q x))).image (G b)) := by
    intro a b hab hbq x hx
    have hxS : x ∈ S := hS'S hx
    ext e
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, hS',
      Set.mem_inter_iff, Set.mem_preimage, Finset.mem_coe]
    constructor
    · rintro ⟨y, ⟨⟨hy, hyT⟩, hyx⟩, rfl⟩
      refine ⟨F q y, ⟨hyT, ?_⟩, hGF b hbq y hy⟩
      rw [hGF a (hab.trans hbq) y hy, hGF a (hab.trans hbq) x hxS, hyx]
    · rintro ⟨c, ⟨hcT, hca⟩, rfl⟩
      obtain ⟨h1, h2⟩ := hrep c (hTL hcT)
      refine ⟨rep c, ⟨⟨h1, by rw [h2]; exact hcT⟩, ?_⟩, rfl⟩
      rw [← hGF a (hab.trans hbq) x hxS]
      exact hca
  -- masses of unions of classes
  have hunion : ∀ U : Finset ℕ, μ.real (S ∩ F q ⁻¹' (U : Set ℕ)) = ∑ c ∈ U, w c := by
    intro U
    have : S ∩ F q ⁻¹' (U : Set ℕ) = ⋃ c ∈ U, (S ∩ F q ⁻¹' {c}) := by
      ext x; simp
    rw [this, measureReal_biUnion_finset]
    · intro c _ c' _ hcc'
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      rintro x ⟨_, hx⟩ ⟨_, hx'⟩
      exact hcc' ((Set.mem_singleton_iff.1 hx).symm.trans (Set.mem_singleton_iff.1 hx'))
    · intro c _
      exact hS.inter (hFm MeasurableSet.of_discrete)
  have hSL : μ.real S = μ.real (S ∩ F q ⁻¹' (L : Set ℕ)) := by
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx, hFq x hx⟩, fun hx => hx.1⟩
  have hcardL : L.card = (F q '' S).ncard := by
    rw [hL, Set.ncard_eq_toFinset_card _ hfin]
  refine ⟨S', hS'S, hS'm, ?_, ?_, ?_⟩
  · rw [hSL, hunion L, hunion T, ← hcardL]
    exact hmass
  · intro a b hab hbq
    rw [himage a (hab.trans hbq), himage b hbq, Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact hmono a b hab hbq
  · intro a b hab hbq x hx
    rw [hdimage a b hab hbq x hx, himage a (hab.trans hbq), himage b hbq, Set.ncard_coe_finset,
      Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact hdesc a b hab hbq (F q x) hx.2

end Submission.Obl.k4_matching_homogeneous_records
