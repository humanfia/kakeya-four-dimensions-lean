import Mathlib
import Submission.Lib.K4ContactTransfer.ContactWitness

/-!
# Structure of the zoomed label tree

* `relFin_inj`: rebased indices of two descendants agree only if their original
  block indices agree, so rebased labels in the same block have disjoint priors;
* `ret_ancestor`: every retained descendant has a retained ancestor at every
  shallower grid level (nesting of the zoomed tree);
* `cover_zoom`: the zoomed law is covered, at every grid level, by the retained
  descendants;
* `contact_zoom`: the normalized contact equation holds almost everywhere for
  the zoomed law.
-/

namespace Submission.Lib.K4ContactTransfer

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel

noncomputable section

theorem relFin_inj {T TQ : ℕ} {j : Fin (2 ^ T)} {j' : Fin (2 ^ T)} {jQ : Fin (2 ^ TQ)}
    (h : interval T j ⊆ interval TQ jQ) (h' : interval T j' ⊆ interval TQ jQ)
    (he : (relFin h : ℕ) = (relFin h' : ℕ)) : j = j' := by
  have h1 := (relIndex_spec h).1
  have h2 := (relIndex_spec h').1
  simp only [relFin, relIndex] at he
  apply Fin.ext
  omega

variable {α : Type} [MeasurableSpace α]

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

/-- Retained descendants of the same level with equal rebased index have disjoint
priors. -/
theorem disjoint_ret {R : ℝ} {jj : Fin I.M} (hats : a.AtlasAt p R I.k (I.depth jj))
    {x x' : I.Ret jj} (hne : x ≠ x')
    (hj : (relFin (I.block_sub x) : ℕ) = (relFin (I.block_sub x') : ℕ)) :
    Disjoint (a.A I.k (I.depth jj) x.1.1) (a.A I.k (I.depth jj) x'.1.1) := by
  have hne' : x.1.1 ≠ x'.1.1 := by
    intro h
    exact hne (Subtype.ext (Subtype.ext h))
  exact hats.disjoint _ _ hne' (relFin_inj (I.block_sub x) (I.block_sub x') hj)

/-- A retained descendant is not light, hence its box is nonempty. -/
theorem ret_box_nonempty (hp : p.Valid) {R : ℝ} {jj : Fin I.M}
    (hats : a.AtlasAt p R I.k (I.depth jj)) (hθ : 0 < I.θ) (x : I.Ret jj) :
    (towerBox (⟨jj, x.1⟩ : I.Label)).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hl := x.2.1
  apply hl
  simp only [towerLight, ZoomInput.box, h, inter_empty, measure_empty]
  apply ENNReal.mul_pos
  · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · exact mul_ne_zero (by simp [q_pos a I.k (I.depth jj)]) (hats.prior_pos hp _)

/-- **Retained ancestors.** -/
theorem ret_ancestor (hp : p.Valid) {R : ℝ} (hatr : a.AtlasAt p R I.k r)
    (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hnest : ∀ j j' : Fin I.M, j < j' → ∀ i : Fin (a.n I.k (I.depth j')),
      ∃ h : Fin (a.n I.k (I.depth j)),
        a.A I.k (I.depth j') i ⊆ a.A I.k (I.depth j) h ∧
          a.block I.k (I.depth j') i ⊆ a.block I.k (I.depth j) h)
    (hnestr : ∀ j : Fin I.M, ∀ i : Fin (a.n I.k (I.depth j)), ∃ h : Fin (a.n I.k r),
      a.A I.k (I.depth j) i ⊆ a.A I.k r h ∧ a.block I.k (I.depth j) i ⊆ a.block I.k r h)
    (hθ : 0 < I.θ) {j₁ j₂ : Fin I.M} (hle : j₁ ≤ j₂) (x : I.Ret j₂) :
    ∃ y : I.Ret j₁, a.A I.k (I.depth j₂) x.1.1 ⊆ a.A I.k (I.depth j₁) y.1.1 ∧
      a.block I.k (I.depth j₂) x.1.1 ⊆ a.block I.k (I.depth j₁) y.1.1 := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · obtain ⟨h, hA, hI⟩ := hnest j₁ j₂ hlt x.1.1
    -- a nonempty box of `x`
    obtain ⟨⟨l, t⟩, hlB, _⟩ := I.ret_box_nonempty hp (hats j₂) hθ x
    have hlA : l ∈ a.A I.k (I.depth j₂) x.1.1 := (hats j₂).B_sub_A _ hlB
    -- `h` descends from `Q`
    have hdesc : h ∈ descSet (a.A I.k (I.depth j₁)) (a.j I.k (I.depth j₁)) (a.A I.k r I.Q)
        (a.T I.k r) (a.j I.k r I.Q) := by
      obtain ⟨h', hA', hI'⟩ := hnestr j₁ h
      by_cases hh : h' = I.Q
      · subst hh; exact mem_descSet.mpr ⟨hA', hI'⟩
      · exfalso
        obtain ⟨t', ht', ht'E⟩ := exists_mem_block_not_dyadic (a.T I.k (I.depth j₂))
          (a.j I.k (I.depth j₂) x.1.1) (dyadicPoints (a.T I.k r)) (dyadicPoints_countable _)
        have h1 : l ∈ a.A I.k r h' := hA' (hA hlA)
        have h2 : l ∈ a.A I.k r I.Q := I.prior_sub x hlA
        have h3 : t' ∈ a.block I.k r h' := hI' (hI ht')
        have h4 : t' ∈ a.block I.k r I.Q := I.block_sub x ht'
        exact ht'E (same_depth_meet hatr hh h1 h2 h3 h4)
    -- it is retained
    have hret : towerRetained (a.mu I.k) I.G I.lv I.box I.wt I.θ I.anc
        (⟨j₁, ⟨h, hdesc⟩⟩ : I.Label) := by
      have hancx : I.anc ⟨j₁, ⟨h, hdesc⟩⟩ ⟨j₂, x.1⟩ := ⟨hlt, hA, hI⟩
      refine ⟨x.2.2 _ hancx, ?_⟩
      intro z hz
      apply x.2.2 z
      exact ⟨hz.1.trans hlt, hA.trans hz.2.1, hI.trans hz.2.2⟩
    exact ⟨⟨⟨h, hdesc⟩, hret⟩, hA, hI⟩
  · subst heq
    exact ⟨x, subset_rfl, subset_rfl⟩

/-- **Coverage.** The zoomed law is covered at every grid level by the
retained descendants. -/
theorem cover_zoom (hcommon : a.Common p) {R : ℝ} (hatr : a.AtlasAt p R I.k r)
    (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hnest : ∀ j j' : Fin I.M, j < j' → ∀ i : Fin (a.n I.k (I.depth j')),
      ∃ h : Fin (a.n I.k (I.depth j)),
        a.A I.k (I.depth j') i ⊆ a.A I.k (I.depth j) h ∧
          a.block I.k (I.depth j') i ⊆ a.block I.k (I.depth j) h)
    (hnestr : ∀ j : Fin I.M, ∀ i : Fin (a.n I.k (I.depth j)), ∃ h : Fin (a.n I.k r),
      a.A I.k (I.depth j) i ⊆ a.A I.k r h ∧ a.block I.k (I.depth j) i ⊆ a.block I.k r h)
    (hGm : MeasurableSet I.G) (hGsub : I.G ⊆ a.B I.k r I.Q ×ˢ a.block I.k r I.Q)
    (jj : Fin I.M) :
    ∀ᵐ z ∂zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W,
      ∃ x : I.Ret jj, z.1 ∈ a.B I.k (I.depth jj) x.1.1 ∧ z.2 ∈ I.zblock x := by
  classical
  have := hcommon.prob I.k
  have hGsub' : I.G ⊆ a.A I.k r I.Q ×ˢ a.block I.k r I.Q := fun z hz =>
    ⟨hatr.B_sub_A _ (hGsub hz).1, (hGsub hz).2⟩
  have hcov := tower_retained_cover (μ := a.mu I.k) (G := I.G) (lv := I.lv) (X := I.box)
    (w := I.wt) (θ := I.θ) (anc := I.anc) (M := I.M)
    (tower_generic (hcommon.dom I.k) (fun j => hats j) hnest I.G)
    (tower_cover (hcommon.dom I.k) hatr (fun j => hats j) (fun j => (hats j).cover)
      hnestr hGsub')
    (fun x y h => h.1)
    (fun x y y' hy hy' hlv hne => tower_anc_unique (fun j => hats j) x y y' hy hy' hlv hne)
  apply ae_zoomLaw _ (I.measurable_keep hats hGm)
  · have : {z : α × ℝ | ∃ x : I.Ret jj, z.1 ∈ a.B I.k (I.depth jj) x.1.1 ∧ z.2 ∈ I.zblock x} =
        ⋃ x : I.Ret jj, (a.B I.k (I.depth jj) x.1.1 ×ˢ I.zblock x) := by
      ext z; simp [mem_prod]
    rw [this]
    exact MeasurableSet.iUnion fun x =>
      ((hats jj).measurable_B _).prod measurableSet_Icc
  · filter_upwards [hcov] with z hz hzk
    obtain ⟨y, hylv, hyret, hyz⟩ := hz hzk (jj : ℕ) jj.2
    rcases y with ⟨jy, iy⟩
    have : jy = jj := Fin.ext hylv
    subst this
    refine ⟨⟨iy, hyret⟩, hyz.1, ?_⟩
    simp only [zoomTime]
    exact (I.mem_zblock ⟨iy, hyret⟩ z.2).mp hyz.2

/-- **Contact.** The normalized contact equation holds almost everywhere for the
zoomed law. -/
theorem contact_zoom (hcommon : a.Common p) {R : ℝ}
    (hats : ∀ j, a.AtlasAt p R I.k (I.depth j)) (hGm : MeasurableSet I.G) {E : ℝ}
    (hcon : ∀ z ∈ I.G, |Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1) 4 +
      Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1) 0| ≤ E) :
    ∀ᵐ z ∂zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W,
      |Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1) 4 + Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1) 0| ≤
        E := by
  have hb := (hcommon I.k).1
  apply ae_zoomLaw _ (I.measurable_keep hats hGm)
  · have hm : Measurable (fun z : α × ℝ => Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) :=
      I.continuous_nCoeff.measurable.comp (hb.comp measurable_fst)
    exact measurableSet_le
      ((((measurable_pi_apply 4).comp hm).add ((measurable_pi_apply 0).comp hm)).abs)
      measurable_const
  · exact ae_of_all _ fun z hz => hcon z (I.keep_subset hz)

end ZoomInput

end

end Submission.Lib.K4ContactTransfer
