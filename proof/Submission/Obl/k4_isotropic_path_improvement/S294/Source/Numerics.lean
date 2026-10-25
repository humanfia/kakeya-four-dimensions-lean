-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.Numerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Per-sample numerics of the relative row packet (session x1088).

* `scalarClauses_of`: the scalar clauses of `RelativeRowPacket` for `θ = (a'/h') ζ^Ep / K^Ep`,
  `ε = θ ζ / K^(Ep+2)`, `pv = θ / K^(Ep+2)`, from `a' ≤ K h'`, `h' ≤ ζ ≤ 1`, `2 ≤ K`, `κ ≤ K`.
* `clock_mono`, `rel_clock_le_zeta`, `rel_thickness_le`: the path's clock and thickness bounds
  at an ancestor level and a deeper child level give `T_a ≤ T_b`, `2^-(T_b - T_a) ≤ ζ` and
  `δ(N, r_b)/δ(N, r_a) ≤ K 2^-(T_b - T_a)`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Clauses
import Submission.Obl.k4_clean_cover_graph_atlas

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- **The scalar clauses.** -/
theorem scalarClauses_of {Ep : ℕ} {Nk L gain loss ζ κ K a' h' : ℝ}
    (ha' : 0 < a') (hh' : 0 < h') (haK : a' ≤ K * h') (hhζ : h' ≤ ζ) (hζ0 : 0 < ζ)
    (hζ1 : ζ ≤ 1) (hK2 : 2 ≤ K) (hκK : κ ≤ K) (hKEp : K ^ Ep ≤ Nk ^ (loss * gain * L)) :
    ScalarClauses Ep Nk L gain loss ζ κ K
      ((a' / h') * ζ ^ Ep / K ^ Ep * ζ / K ^ (Ep + 2))
      ((a' / h') * ζ ^ Ep / K ^ Ep / K ^ (Ep + 2))
      ((a' / h') * ζ ^ Ep / K ^ Ep) a' h' := by
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKp : ∀ n : ℕ, 1 ≤ K ^ n := fun n => one_le_pow₀ hK1
  have hζp : ζ ^ Ep ≤ 1 := pow_le_one₀ hζ0.le hζ1
  have hah : a' / h' ≤ K := by rw [div_le_iff₀ hh']; linarith
  have hah0 : 0 < a' / h' := div_pos ha' hh'
  set θ := (a' / h') * ζ ^ Ep / K ^ Ep with hθ
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθK : θ ≤ a' / h' := by
    rw [hθ, div_le_iff₀ (by positivity)]
    calc a' / h' * ζ ^ Ep ≤ a' / h' * 1 := by gcongr
      _ ≤ a' / h' * K ^ Ep := by gcongr; exact hKp Ep
  have hKE2 : K ≤ K ^ (Ep + 2) := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ (Ep + 2) := pow_le_pow_right₀ hK1 (by omega)
  have hK2le : K ^ Ep * K ^ 2 = K ^ (Ep + 2) := (pow_add K Ep 2).symm
  refine ⟨by positivity, ?_, ?_, ha', haK, hhζ, hζ1, hK2, hκK, hKEp, rfl, ?_, by positivity, ?_⟩
  · -- ε ≤ ζ
    rw [div_le_iff₀ (by positivity)]
    calc θ * ζ ≤ K * ζ := by gcongr; linarith
      _ ≤ ζ * K ^ (Ep + 2) := by nlinarith
  · -- ε ≤ (a'/h') ζ
    rw [div_le_iff₀ (by positivity)]
    calc θ * ζ ≤ a' / h' * ζ := by gcongr
      _ ≤ a' / h' * ζ * K ^ (Ep + 2) := by
        have := hKp (Ep + 2)
        have : 0 ≤ a' / h' * ζ := by positivity
        nlinarith
  · -- K^Ep ε ≤ θ
    rw [mul_div_assoc', div_le_iff₀ (by positivity), ← hK2le]
    have h1 : 1 ≤ K ^ 2 := hKp 2
    have : 0 ≤ K ^ Ep := by positivity
    calc K ^ Ep * (θ * ζ) ≤ K ^ Ep * (θ * 1) := by gcongr
      _ = θ * K ^ Ep * 1 := by ring
      _ ≤ θ * (K ^ Ep * K ^ 2) := by
        rw [mul_assoc]; gcongr
  · -- K^Ep pv ≤ θ
    rw [mul_div_assoc', div_le_iff₀ (by positivity), ← hK2le]
    have h1 : 1 ≤ K ^ 2 := hKp 2
    have : 0 ≤ K ^ Ep := by positivity
    calc K ^ Ep * θ = θ * K ^ Ep * 1 := by ring
      _ ≤ θ * (K ^ Ep * K ^ 2) := by
        rw [mul_assoc]; gcongr

/-- The dyadic clock is monotone between levels whose path exponents are separated. -/
theorem clock_mono {N L κ₁ sa sb δ₀ : ℝ} {Ta Tb : ℕ} (hN : 1 < N) (hL : 0 ≤ L)
    (ha : (2 : ℝ) ^ Ta ≤ N ^ ((κ₁ * sa + δ₀) * L))
    (hb : N ^ ((κ₁ * sb - δ₀) * L) ≤ (2 : ℝ) ^ Tb)
    (hsep : κ₁ * sa + δ₀ ≤ κ₁ * sb - δ₀) : Ta ≤ Tb := by
  have h : (2 : ℝ) ^ Ta ≤ (2 : ℝ) ^ Tb :=
    ha.trans ((Real.rpow_le_rpow_of_exponent_le hN.le (by nlinarith)).trans hb)
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h

/-- The relative clock is below `ζ = δ(N, precision gain L)` once the child is deep enough. -/
theorem rel_clock_le_zeta {N L κ₁ sa sb δ₀ precision gain : ℝ} {Ta Tb : ℕ} (hN : 1 < N)
    (hL : 0 ≤ L) (hTab : Ta ≤ Tb)
    (ha : (2 : ℝ) ^ Ta ≤ N ^ ((κ₁ * sa + δ₀) * L))
    (hb : N ^ ((κ₁ * sb - δ₀) * L) ≤ (2 : ℝ) ^ Tb)
    (hsep : precision * gain + 2 * δ₀ ≤ κ₁ * (sb - sa)) :
    ((2 : ℝ) ^ (Tb - Ta))⁻¹ ≤ O204.Split.δ N (precision * gain * L) := by
  have hNp : 0 < N := by linarith
  have hlow : N ^ (-(precision * gain * L)) ≤ O204.Split.δ N (precision * gain * L) :=
    (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp _).1
  refine le_trans ?_ hlow
  have hrel : ((2 : ℝ) ^ (Tb - Ta))⁻¹ = (2 : ℝ) ^ Ta / (2 : ℝ) ^ Tb := by
    rw [pow_sub₀ (2 : ℝ) (by norm_num) hTab]; field_simp
  rw [hrel, div_le_iff₀ (by positivity)]
  calc (2 : ℝ) ^ Ta ≤ N ^ ((κ₁ * sa + δ₀) * L) := ha
    _ ≤ N ^ (-(precision * gain * L) + (κ₁ * sb - δ₀) * L) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (by nlinarith)
    _ = N ^ (-(precision * gain * L)) * N ^ ((κ₁ * sb - δ₀) * L) := Real.rpow_add hNp _ _
    _ ≤ N ^ (-(precision * gain * L)) * (2 : ℝ) ^ Tb := by gcongr

/-- The relative thickness is at most `K` times the relative clock, for `K ≥ 2 N^(4 δ₀ L)`. -/
theorem rel_thickness_le {N L κ₁ sa sb δ₀ ra rb K : ℝ} {Ta Tb : ℕ} (hN : 1 < N)
    (hL : 0 ≤ L) (hκ1 : κ₁ ≤ 1) (hTab : Ta ≤ Tb)
    (hra : ra ≤ (sa + δ₀) * L) (hrb : (sb - δ₀) * L ≤ rb) (hsab : sa ≤ sb)
    (ha : N ^ ((κ₁ * sa - δ₀) * L) ≤ (2 : ℝ) ^ Ta)
    (hb : (2 : ℝ) ^ Tb ≤ N ^ ((κ₁ * sb + δ₀) * L))
    (hK : 2 * N ^ (4 * δ₀ * L) ≤ K) :
    O204.Split.δ N rb / O204.Split.δ N ra ≤ K * ((2 : ℝ) ^ (Tb - Ta))⁻¹ := by
  have hNp : 0 < N := by linarith
  obtain ⟨hla, -⟩ := Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp ra
  obtain ⟨-, hub⟩ := Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp rb
  have hδa : 0 < O204.Split.δ N ra := (Real.rpow_pos_of_pos hNp _).trans_le hla
  have hrel : ((2 : ℝ) ^ (Tb - Ta))⁻¹ = (2 : ℝ) ^ Ta / (2 : ℝ) ^ Tb := by
    rw [pow_sub₀ (2 : ℝ) (by norm_num) hTab]; field_simp
  rw [div_le_iff₀ hδa, hrel]
  -- `δ_b ≤ 2 N^(-rb)`, `N^(-ra) ≤ δ_a`, `2^Ta ≥ N^((κ₁ sa - δ₀) L)`, `2^Tb ≤ N^((κ₁ sb + δ₀) L)`
  have hNa : N ^ (-((sa + δ₀) * L)) ≤ O204.Split.δ N ra :=
    (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)).trans hla
  have hNb : O204.Split.δ N rb ≤ 2 * N ^ (-((sb - δ₀) * L)) :=
    hub.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)) (by norm_num))
  have hTbpos : (0 : ℝ) < 2 ^ Tb := by positivity
  -- target: δ_b ≤ K (2^Ta / 2^Tb) δ_a
  have key : 2 * N ^ (-((sb - δ₀) * L)) * (2 : ℝ) ^ Tb ≤
      K * (2 : ℝ) ^ Ta * N ^ (-((sa + δ₀) * L)) := by
    calc 2 * N ^ (-((sb - δ₀) * L)) * (2 : ℝ) ^ Tb
        ≤ 2 * N ^ (-((sb - δ₀) * L)) * N ^ ((κ₁ * sb + δ₀) * L) := by gcongr
      _ = 2 * N ^ (4 * δ₀ * L) * N ^ ((κ₁ * sa - δ₀) * L) * N ^ (-((sa + δ₀) * L)) *
            N ^ (-((1 - κ₁) * (sb - sa)) * L) := by
          rw [mul_assoc 2, ← Real.rpow_add hNp, mul_assoc (2 * N ^ (4 * δ₀ * L)),
            mul_assoc (2 * N ^ (4 * δ₀ * L)), ← Real.rpow_add hNp, ← Real.rpow_add hNp,
            mul_assoc 2, ← Real.rpow_add hNp]
          congr 2
          ring
      _ ≤ K * N ^ ((κ₁ * sa - δ₀) * L) * N ^ (-((sa + δ₀) * L)) * 1 := by
          have h2 : N ^ (-((1 - κ₁) * (sb - sa)) * L) ≤ 1 := by
            apply Real.rpow_le_one_of_one_le_of_nonpos hN.le
            have : 0 ≤ (1 - κ₁) * (sb - sa) := mul_nonneg (by linarith) (by linarith)
            nlinarith
          have hK0 : 0 ≤ K := by
            have : 0 ≤ 2 * N ^ (4 * δ₀ * L) := by positivity
            linarith
          calc 2 * N ^ (4 * δ₀ * L) * N ^ ((κ₁ * sa - δ₀) * L) * N ^ (-((sa + δ₀) * L)) *
                N ^ (-((1 - κ₁) * (sb - sa)) * L)
              ≤ K * N ^ ((κ₁ * sa - δ₀) * L) * N ^ (-((sa + δ₀) * L)) *
                N ^ (-((1 - κ₁) * (sb - sa)) * L) := by gcongr
            _ ≤ K * N ^ ((κ₁ * sa - δ₀) * L) * N ^ (-((sa + δ₀) * L)) * 1 := by gcongr
      _ ≤ K * (2 : ℝ) ^ Ta * N ^ (-((sa + δ₀) * L)) := by
          rw [mul_one]
          have hK0 : 0 ≤ K := by
            have : 0 ≤ 2 * N ^ (4 * δ₀ * L) := by positivity
            linarith
          gcongr
  have hKa : 0 ≤ K * (2 : ℝ) ^ Ta := by
    have : 0 ≤ 2 * N ^ (4 * δ₀ * L) := by positivity
    have : 0 ≤ K := by linarith
    positivity
  calc O204.Split.δ N rb ≤ 2 * N ^ (-((sb - δ₀) * L)) := hNb
    _ = 2 * N ^ (-((sb - δ₀) * L)) * (2 : ℝ) ^ Tb / (2 : ℝ) ^ Tb := by field_simp
    _ ≤ K * (2 : ℝ) ^ Ta * N ^ (-((sa + δ₀) * L)) / (2 : ℝ) ^ Tb := by gcongr
    _ ≤ K * (2 : ℝ) ^ Ta * O204.Split.δ N ra / (2 : ℝ) ^ Tb := by gcongr
    _ = K * ((2 : ℝ) ^ Ta / (2 : ℝ) ^ Tb) * O204.Split.δ N ra := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
