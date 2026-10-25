-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormMain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormParameters
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormBridge

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_separated_cover_refinement (Dense Weak Strong)

theorem norm_weak_mono {η ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Weak η δ n x v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε) :
    Weak ε δ n x v := by
  have hp : δ ^ (-η) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηε)
  intro r hr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, hcov⟩ := h r hr hr1
  exact ⟨ρ, hrρ, hρ1, hρr.trans (mul_le_mul_of_nonneg_right hp (hδ.le.trans hr)),
    k, hk, z, w, CoverAt.mono_K hcov hp⟩

/-- The refinement theorem may always use an input error at most `1/4`. -/
theorem norm_refinement {ε : ℝ} (hε : 0 < ε) :
    ∃ β d1 : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧ 0 < d1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ (1 / 100 : ℝ) →
        ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
          Dense β δ n x v Y → Weak β δ n x v →
          ∃ (m : ℕ) (a : Fin m → Fin n), Function.Injective a ∧
            Dense ε δ m (fun i => x (a i)) (fun i => v (a i)) (fun i => Y (a i)) ∧
            Strong ε δ m (fun i => x (a i)) (fun i => v (a i)) := by
  obtain ⟨η, d1, hη, hd1, hR⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.refinement ε hε
  refine ⟨min η (1 / 4), d1, lt_min hη (by norm_num), min_le_right _ _, hd1, ?_⟩
  intro δ hδ hδd hδ100 n x v Y hD hW
  exact hR δ hδ hδd hδ100 n x v Y
    ((family_of_dense hD).mono_error hδ (by linarith only [hδ100]) (min_le_left _ _))
    (norm_weak_mono hW hδ (by linarith only [hδ100]) (min_le_left _ _))

/-- Mild rescaling turns weak global and local grains into the normalized frozen conclusion. -/
theorem norm_of_ggx {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hGG : GGX σ) : Grains σ := by
  intro ε d0 hε hd0
  obtain ⟨β, d1, hβ, hβ4, hd1, hR⟩ := norm_refinement (half_pos hε)
  obtain ⟨η, L, dc, hη, hL, hdc, hparams⟩ :=
    normalization_parameters hβ hβ4 hε (lt_min hd0 hd1)
  obtain ⟨δ, hδ, hδc, hδ100, n, x, v, Y, hF, hS, f, V, hf, hslice, hVu, hVp, hVL, hloc⟩ :=
    hGG η dc hη hdc
  have hδ1 : δ ≤ 1 := by linarith only [hδ100]
  obtain ⟨hB, hcompact, hvolC⟩ := hparams δ hδ hδ1 hδc
  let lam : ℝ := 3 * δ ^ (-η)
  have hCpos : 0 < δ ^ (-η) := Real.rpow_pos_of_pos hδ _
  have hC1 : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith only [hη])
  have hlam : 1 ≤ lam := by dsimp [lam]; linarith only [hC1]
  have hlam0 : 0 < lam := by linarith only [hlam]
  have hnew : 0 < lam * δ := mul_pos hlam0 hδ
  have hnew100 : lam * δ ≤ 1 / 100 := hB.tiny.trans (by norm_num)
  obtain ⟨c, Q, -, hD, hW⟩ :=
    zoomed_dense_weak (lam := lam) (δ' := lam * δ) (K := normColors lam)
      (t := normRet δ η lam L) hδ hδ100 hη hβ hL rfl rfl rfl rfl hF hS
      hB.tiny hB.first hB.last hB.step hB.start hB.coarse hB.count hB.density hB.frostman hB.top
  have hCo : δ ^ (-η) ≤ (lam * δ) ^ (-ε) := by
    have hh : δ ^ (-η) ≤ 32 * δ ^ (-η) := by linarith only [hCpos]
    exact hh.trans hvolC
  obtain ⟨m, x', v', Y', hbody⟩ :=
    zoomed_grains_body (δ' := lam * δ) (η₁ := β) (ε := ε / 2) (ηo := ε)
      hσ0 hσ1 hδ hlam rfl hCpos.le (le_refl (3 * δ ^ (-η))) hCpos.le
      hF hf hslice hVu hVp hVL hloc hD hW hR
      (hB.scale.trans (min_le_right _ _)) hnew100 (by linarith only [hε]) hcompact hCo hvolC
  exact ⟨lam * δ, hnew, hB.scale.trans (min_le_left _ _), hnew100, m, x', v', Y', hbody⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
