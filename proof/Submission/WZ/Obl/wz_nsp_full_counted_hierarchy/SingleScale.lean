-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.SingleScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.CopiedHierarchy
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Arithmetic

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The supplied single-scale theorem, with the tube formula unfolded. -/
abbrev SingleScale : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (r ρ M L : ℝ) (K n : ℕ) (y w : Fin K → Space) (x v : Fin n → Space)
      (g : Fin n → Fin K),
      0 < r → r ≤ ρ → ρ ≤ 1 → 1 ≤ M →
      (∀ k, ‖w k‖ = 1 ∧ (Set.ncard {i | g i = k} : ℝ) ≤ M) →
      (∀ i, ‖v i‖ = 1 ∧ Tube r (x i) (v i) ⊆ Metric.ball 0 1 ∧
        Tube r (x i) (v i) ⊆ Tube ρ (y (g i)) (w (g i))) →
      (∀ k W, Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {i | g i = k ∧ Tube r (x i) (v i) ⊆ W} : ℝ) * r ^ 2) ≤
        ENNReal.ofReal L * volume W) →
      ∃ (N : ℕ) (A : Fin N → (Space ≃ᵃⁱ[ℝ] Space)),
        ρ ^ 2 ≤ (N : ℝ) * M * r ^ 2 ∧
        (N : ℝ) * M * r ^ 2 ≤ ρ ^ 2 + M * r ^ 2 ∧
        (∀ a p, ‖p‖ < 1 → ‖A a p - p‖ ≤ ρ) ∧
        ∀ k W, Convex ℝ W →
          ENNReal.ofReal ((Set.ncard {q : Fin N × Fin n | g q.2 = k ∧
            Tube r (A q.1 (x q.2)) ((A q.1).linear (v q.2)) ⊆ W} : ℝ) * r ^ 2) ≤
          ENNReal.ofReal (C * r ^ (-ε) * Real.log (2 + (K : ℝ)) * L) * volume W

/-- Choose all finite lists of motions simultaneously. The unused stages are
filled with an identity motion so that the tower has natural-number indices. -/
theorem choose_stage_copies (hSS : SingleScale) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (r ρ M L : ℕ → ℝ) (n : ℕ → ℕ)
      (x v : ∀ j, Fin (n j) → Space) (f : ∀ j, Fin (n (j + 1)) → Fin (n j)),
      (∀ j, j < J → 0 < r (j + 1) ∧ r (j + 1) ≤ ρ j ∧ ρ j ≤ 1 ∧ 1 ≤ M j) →
      (∀ j, j < J → ∀ k, ‖v j k‖ = 1 ∧ (Set.ncard {i | f j i = k} : ℝ) ≤ M j) →
      (∀ j, j < J → ∀ i, ‖v (j + 1) i‖ = 1 ∧
        Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆ Metric.ball 0 1 ∧
        Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆
          Tube (ρ j) (x j (f j i)) (v j (f j i))) →
      (∀ j, j < J → ∀ k W, Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {i | f j i = k ∧
          Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
          ENNReal.ofReal (L j) * volume W) →
      ∃ (D : ℕ → ℕ) (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space)),
        ∀ j, j < J → 0 < D j ∧
        (ρ j) ^ 2 ≤ (D j : ℝ) * M j * (r (j + 1)) ^ 2 ∧
        (D j : ℝ) * M j * (r (j + 1)) ^ 2 ≤ (ρ j) ^ 2 + M j * (r (j + 1)) ^ 2 ∧
        (∀ a p, ‖p‖ < 1 → ‖A j a p - p‖ ≤ ρ j) ∧
        ∀ k W, Convex ℝ W →
          ENNReal.ofReal ((Set.ncard {q : Fin (D j) × Fin (n (j + 1)) |
            f j q.2 = k ∧ Tube (r (j + 1)) (A j q.1 (x (j + 1) q.2))
              ((A j q.1).linear (v (j + 1) q.2)) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
          ENNReal.ofReal (C * (r (j + 1)) ^ (-ε) * Real.log (2 + (n j : ℝ)) * L j) * volume W := by
  classical
  obtain ⟨C, hC, h⟩ := hSS ε hε
  refine ⟨C, hC, ?_⟩
  intro J r ρ M L n x v f hr hv hx hlocal
  have hex (j : ℕ) : ∃ (D : ℕ) (A : Fin D → (Space ≃ᵃⁱ[ℝ] Space)),
      j < J → 0 < D ∧ (ρ j) ^ 2 ≤ (D : ℝ) * M j * (r (j + 1)) ^ 2 ∧
      (D : ℝ) * M j * (r (j + 1)) ^ 2 ≤ (ρ j) ^ 2 + M j * (r (j + 1)) ^ 2 ∧
      (∀ a p, ‖p‖ < 1 → ‖A a p - p‖ ≤ ρ j) ∧
      ∀ k W, Convex ℝ W → ENNReal.ofReal ((Set.ncard {q : Fin D × Fin (n (j + 1)) |
        f j q.2 = k ∧ Tube (r (j + 1)) (A q.1 (x (j + 1) q.2))
          ((A q.1).linear (v (j + 1) q.2)) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
        ENNReal.ofReal (C * (r (j + 1)) ^ (-ε) * Real.log (2 + (n j : ℝ)) * L j) * volume W := by
    by_cases hj : j < J
    · obtain ⟨D, A, hlo, hhi, hmove, hcount⟩ := h
        (r (j + 1)) (ρ j) (M j) (L j) (n j) (n (j + 1))
        (x j) (v j) (x (j + 1)) (v (j + 1)) (f j)
        (hr j hj).1 (hr j hj).2.1 (hr j hj).2.2.1 (hr j hj).2.2.2
        (hv j hj) (hx j hj) (hlocal j hj)
      exact ⟨D, A, fun _ => ⟨copies_pos ((hr j hj).1.trans_le (hr j hj).2.1) hlo,
        hlo, hhi, hmove, hcount⟩⟩
    · exact ⟨1, fun _ => AffineIsometryEquiv.refl ℝ Space, fun h => (hj h).elim⟩
  choose D A hstage using hex
  exact ⟨D, A, hstage⟩

/-- The original buffer contains the moved children after the motion consumes
at most half of the parent radius. -/
theorem local_moved_containment {r ρ R : ℝ} (A : Space ≃ᵃⁱ[ℝ] Space)
    {x v y w : Space} (hsub : Tube r x v ⊆ Tube ρ y w)
    (hcore : segment ℝ y (y + w) ⊆ Metric.ball 0 1)
    (hmove : ∀ p : Space, ‖p‖ < 1 → ‖A p - p‖ ≤ ρ) (hbuffer : 2 * ρ ≤ R) :
    Tube r (A x) (A.linear v) ⊆ Tube R y w := by
  apply (rigid_containment A hsub).trans
  apply (moved_tube_subset A y w (fun p hp => hmove p (by simpa using hcore hp))).trans
  apply Metric.thickening_mono
  linarith

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
