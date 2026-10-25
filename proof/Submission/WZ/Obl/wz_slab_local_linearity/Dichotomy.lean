-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.Dichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.FiniteCovering
import Submission.WZ.Obl.wz_slab_local_linearity.GraphLine
import Submission.WZ.Obl.wz_slab_local_linearity.HeightCells

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric

/-- The plane covering hypothesis, with open localization balls as in the frozen statement. -/
def PlaneAD (δ C : ℝ) (F : Set Plane) : Prop :=
  ∀ (x : Plane) (ρ r : ℝ), δ ≤ ρ → ρ ≤ r → ∃ (m : ℕ) (c : Fin m → Plane),
    F ∩ ball x r ⊆ ⋃ j, closedBall (c j) ρ ∧ (m : ℝ) ≤ C * (r / ρ)

/-- The precise projection dichotomy assumed by the slab theorem. -/
def ProjectionDichotomy : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ F G : Set Plane,
    (∀ a ∈ F, ∀ i : Fin 2, 0 ≤ a i ∧ a i ≤ 1) →
    (∀ b ∈ G, ∀ i : Fin 2, 0 ≤ b i ∧ b i ≤ 1) →
    PlaneAD δ (δ ^ (-η)) F → PlaneAD δ (δ ^ (-η)) G →
    ((∃ (e b₀ : Plane) (c : ℝ), ‖e‖ = 1 ∧
      CoverLower (thickening δ {a | inner ℝ a e = c} ∩ F) δ (δ ^ (ε - 1)) ∧
      CoverLower (thickening δ (range (fun t : ℝ => b₀ + t • e)) ∩ G) δ (δ ^ (ε - 1))) ∨
    (∀ Q : Set (Plane × Plane × Plane), Q ⊆ F ×ˢ (G ×ˢ G) →
      CoverLower Q δ (δ ^ (η - 3)) → ∃ ρ a L : ℝ, δ ≤ ρ ∧ δ ^ (-η) * ρ ≤ L ∧
      CoverLower (Icc a (a + L) ∩ {t : ℝ | ∃ h ∈ Q, t = inner ℝ h.1 (h.2.1 - h.2.2)})
        ρ ((L / ρ) ^ (1 - ε))))

/-- The finite-family line consequence used by the cell argument. -/
def FiniteDichotomy (σ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (K J : Finset ℤ) (a b : ℤ → Plane) (T : Finset (ℤ × ℤ × ℤ)) (D : Set ℝ),
    (∀ k ∈ K, ∀ i : Fin 2, 0 ≤ a k i ∧ a k i ≤ 1) →
    (∀ j ∈ J, ∀ i : Fin 2, 0 ≤ b j i ∧ b j i ≤ 1) →
    ∀ N : ℝ, 1 ≤ N →
    (∀ k ∈ K, ((K.filter fun k' => dist (a k) (a k') ≤ 2 * δ).card : ℝ) ≤ N) →
    (∀ j ∈ J, ((J.filter fun j' => dist (b j) (b j') ≤ 2 * δ).card : ℝ) ≤ N) →
    PlaneAD δ (δ ^ (-η)) (a '' (K : Set ℤ)) → PlaneAD δ (δ ^ (-η)) (b '' (J : Set ℤ)) →
    T ⊆ K ×ˢ (J ×ˢ J) → N ^ 3 * δ ^ (η - 3) ≤ (T.card : ℝ) →
    IntervalAD δ (1 - σ) (δ ^ (-η)) D →
    (∀ t ∈ T, inner ℝ (a t.1) (b t.2.1 - b t.2.2) ∈ D) →
    ∃ (e : Plane) (c : ℝ), ‖e‖ = 1 ∧
      δ ^ (ε - 1) ≤ ((K.filter fun k => |inner ℝ (a k) e - c| < δ).card : ℝ)

lemma PlaneAD.mono_constant {δ C C' : ℝ} {F : Set Plane}
    (hδ : 0 < δ) (hC : C ≤ C') (h : PlaneAD δ C F) : PlaneAD δ C' F := by
  intro x ρ r hδρ hρr
  obtain ⟨m, c, hc, hm⟩ := h x ρ r hδρ hρr
  have hρ : 0 ≤ ρ := hδ.le.trans hδρ
  exact ⟨m, c, hc, hm.trans (mul_le_mul_of_nonneg_right hC (div_nonneg (hρ.trans hρr) hρ))⟩

/-- Passing from the geometric projection dichotomy to its finite indexed form. -/
theorem finiteDichotomy_of_projection (hproj : ProjectionDichotomy) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < 1) : FiniteDichotomy σ := by
  classical
  intro ε hε
  let ε' := min ε (σ / 2)
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'σ : ε' ≤ σ / 2 := min_le_right _ _
  obtain ⟨η₁, δ₁, hη₁, hδ₁, hP⟩ := hproj ε' hε'
  let η := η₁ * σ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hηle : η ≤ η₁ := by dsimp [η]; nlinarith
  refine ⟨η, min δ₁ (1 / 2), hη, lt_min hδ₁ (by norm_num), ?_⟩
  intro δ hδ hδ₀ K J a b T D hKa hJb N hN hmultA hmultB hADa hADb hT hcard hD hdot
  have hδ1 : δ < 1 := lt_of_le_of_lt (hδ₀.trans (min_le_right _ _)) (by norm_num)
  have hC : δ ^ (-η) ≤ δ ^ (-η₁) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (neg_le_neg hηle)
  have hFunit : ∀ p ∈ a '' (K : Set ℤ), ∀ i : Fin 2, 0 ≤ p i ∧ p i ≤ 1 := by
    rintro p ⟨k, hk, rfl⟩
    exact hKa k hk
  have hGunit : ∀ p ∈ b '' (J : Set ℤ), ∀ i : Fin 2, 0 ≤ p i ∧ p i ≤ 1 := by
    rintro p ⟨j, hj, rfl⟩
    exact hJb j hj
  rcases hP δ hδ (hδ₀.trans (min_le_left _ _)) _ _ hFunit hGunit
      (hADa.mono_constant hδ hC) (hADb.mono_constant hδ hC) with hline | hexp
  · obtain ⟨e, _, c, he, hline, _⟩ := hline
    refine ⟨e, c, he, ?_⟩
    have hcount : δ ^ (ε' - 1) ≤
        ((K.filter fun k => |inner ℝ (a k) e - c| < δ).card : ℝ) := by
      apply hline.le_card_of_finset_image hδ.le _ a
      rintro p ⟨hp, k, hk, rfl⟩
      exact ⟨k, Finset.mem_filter.mpr ⟨hk, abs_inner_sub_lt_of_mem_thickening he hp⟩, rfl⟩
    exact (Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)).trans hcount
  · let Q : Set (Plane × Plane × Plane) :=
      (fun t : ℤ × ℤ × ℤ => (a t.1, b t.2.1, b t.2.2)) '' (T : Set _)
    have hQ : Q ⊆ (a '' (K : Set ℤ)) ×ˢ ((b '' (J : Set ℤ)) ×ˢ (b '' (J : Set ℤ))) := by
      rintro p ⟨t, ht, rfl⟩
      have ht' := hT ht
      simp only [Finset.mem_product] at ht'
      exact ⟨⟨t.1, ht'.1, rfl⟩, ⟨t.2.1, ht'.2.1, rfl⟩, ⟨t.2.2, ht'.2.2, rfl⟩⟩
    have hQlower : CoverLower Q δ (δ ^ (η₁ - 3)) := by
      apply triple_coverLower_of_card K J a b T (by linarith) hT hmultA hmultB
      calc
        N ^ 3 * δ ^ (η₁ - 3) ≤ N ^ 3 * δ ^ (η - 3) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)) (by positivity)
        _ ≤ (T.card : ℝ) := hcard
    let P : Set ℝ := {u | ∃ q ∈ Q, u = inner ℝ q.1 (q.2.1 - q.2.2)}
    have hPD : P ⊆ D := by
      rintro u ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact hdot t ht
    have hPAd : IntervalAD δ (1 - σ) (δ ^ (-η)) P := hD.mono hPD
    obtain ⟨r, v, L, hδr, hL, hlower⟩ := hexp Q hQ hQlower
    have hM : 1 ≤ δ ^ (-η₁) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1.le (by linarith)
    have hgap : δ ^ (-η) < (δ ^ (-η₁)) ^ ((1 - ε') - (1 - σ)) := by
      rw [← Real.rpow_mul hδ.le]
      apply Real.rpow_lt_rpow_of_exponent_gt hδ hδ1
      dsimp [η]
      nlinarith
    exact False.elim (hPAd.no_expansion hδr (hδ.trans_le hδr) hM hL
      (by linarith) hgap hlower)

end WangZahlLot.Obl.wz_slab_local_linearity
