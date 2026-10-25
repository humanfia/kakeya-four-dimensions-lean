-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyScalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Scalar

namespace WangZahlLot.Obl.wz_flat_factored_improvement

noncomputable def bodyWeight (σ w m l P n : ℝ) : ℝ :=
  m ^ (-1 + 3 / 2 * σ) * l ^ (-σ) * P ^ (-σ) * n ^ (1 - σ) * w ^ (1 - σ / 2)

noncomputable def bodyCellFactor (σ u ε A p B h τ d m l n P w : ℝ) : ℝ :=
  A * (384 : ℝ) ^ (-1 + 3 / 2 * σ) * (49152 : ℝ) ^ (-σ) * d ^ p *
    (B * h) ^ (u + ε) * (h * τ) ^ σ * τ * m ^ (-1 + 3 / 2 * σ) *
    l ^ (-σ) * n ^ (-σ) * P ^ (-σ) * w ^ (1 - σ / 2)

theorem bodyCellFactor_pos {σ u ε A p B h τ d m l n P w : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hh : 0 < h) (hτ : 0 < τ) (hd : 0 < d)
    (hm : 0 < m) (hl : 0 < l) (hn : 0 < n) (hP : 0 < P) (hw : 0 < w) :
    0 < bodyCellFactor σ u ε A p B h τ d m l n P w := by
  unfold bodyCellFactor
  positivity

theorem packet_ratio_lower {D ρ q N w l n P : ℝ}
    (hD : 0 < D) (hρ : 0 < ρ) (hq : 0 < q) (hN : 0 < N)
    (hw : 0 < w) (hl : 0 < l) (hn : 0 < n) (hP : 0 < P)
    (hslab : N * q ≤ 128 * l * n * Real.sqrt D)
    (hpack : Real.sqrt q * w ≤ P * D * (384 * ρ ^ 2)) :
    (49152 * l * n * P)⁻¹ ≤
      (D * Real.sqrt D * ρ ^ 2) / (N * q * Real.sqrt q * w) := by
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hh := mul_le_mul hslab hpack (by positivity : 0 ≤ Real.sqrt q * w)
    (by positivity : 0 ≤ 128 * l * n * Real.sqrt D)
  nlinarith only [hh]

theorem packet_profile_factorization {σ u ε A d p ρ m D q w h τ N : ℝ}
    (hA : 0 < A) (hd : 0 < d) (hρ : 0 < ρ) (hm : 0 < m) (hD : 0 < D)
    (hq : 0 < q) (hw : 0 < w) (hh : 0 < h) (hτ : 0 < τ) (hN : 0 < N) :
    D * profile σ u ε (A * d ^ p) ρ (384 * m * D * ρ ^ 2 / (q * w)) (h * τ)⁻¹ N =
      A * d ^ p * ρ ^ (u + ε) * (384 : ℝ) ^ (-1 + 3 / 2 * σ) *
      m ^ (-1 + 3 / 2 * σ) * (h * τ) ^ σ * (N * q) * w ^ (1 - σ / 2) *
      ((D * Real.sqrt D * ρ ^ 2) / (N * q * Real.sqrt q * w)) ^ σ := by
  unfold profile
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv,
    Real.log_rpow, Real.log_pow, Real.log_sqrt]
  ring

theorem body_packet_scalar {σ u ε A d p ρ m D q w h τ N B l n P I : ℝ}
    (hσ : 0 ≤ σ) (hu : 0 ≤ u + ε) (hA : 0 < A) (hd : 0 < d)
    (hρ : 0 < ρ) (hm : 0 < m) (hD : 0 < D) (hq : 0 < q) (hw : 0 < w)
    (hh : 0 < h) (hτ : 0 < τ) (hN : 0 < N) (hB : 0 < B)
    (hl : 0 < l) (hn : 0 < n) (hP : 0 < P) (hI : 0 ≤ I)
    (hscale : B * h ≤ ρ) (hret : τ * I ≤ N * q)
    (hslab : N * q ≤ 128 * l * n * Real.sqrt D)
    (hpack : Real.sqrt q * w ≤ P * D * (384 * ρ ^ 2)) :
    A * (384 : ℝ) ^ (-1 + 3 / 2 * σ) * (49152 : ℝ) ^ (-σ) * d ^ p *
      (B * h) ^ (u + ε) * (h * τ) ^ σ * τ * m ^ (-1 + 3 / 2 * σ) *
      l ^ (-σ) * n ^ (-σ) * P ^ (-σ) * w ^ (1 - σ / 2) * I ≤
    D * profile σ u ε (A * d ^ p) ρ (384 * m * D * ρ ^ 2 / (q * w)) (h * τ)⁻¹ N := by
  rw [packet_profile_factorization hA hd hρ hm hD hq hw hh hτ hN]
  have hratio := packet_ratio_lower hD hρ hq hN hw hl hn hP hslab hpack
  have hratioPow := Real.rpow_le_rpow (by positivity : 0 ≤ (49152 * l * n * P)⁻¹) hratio hσ
  have hscalePow := Real.rpow_le_rpow (mul_pos hB hh).le hscale hu
  have he : A * (384 : ℝ) ^ (-1 + 3 / 2 * σ) * (49152 : ℝ) ^ (-σ) * d ^ p *
      (B * h) ^ (u + ε) * (h * τ) ^ σ * τ * m ^ (-1 + 3 / 2 * σ) *
      l ^ (-σ) * n ^ (-σ) * P ^ (-σ) * w ^ (1 - σ / 2) * I =
      A * d ^ p * (B * h) ^ (u + ε) * (384 : ℝ) ^ (-1 + 3 / 2 * σ) *
      m ^ (-1 + 3 / 2 * σ) * (h * τ) ^ σ * (τ * I) * w ^ (1 - σ / 2) *
      ((49152 * l * n * P)⁻¹) ^ σ := by
    rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    simp only [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 49152 * l * n) hP.le,
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 49152 * l) hn.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 49152) hl.le]
    ring
  rw [he]
  gcongr

theorem body_sum_factorization {σ u ε A p B δ s c t m l n P w : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ) (hc : 0 < c) (ht : 0 < t)
    (hm : 0 < m) (hl : 0 < l) (hn : 0 < n) (hP : 0 < P) (hw : 0 < w) :
    bodyCellFactor σ u ε A p B (δ ^ s) (t * δ ^ s) (c * (δ ^ s) ^ 9) m l n P w *
        (δ ^ s * n) =
      (A * (384 : ℝ) ^ (-1 + 3 / 2 * σ) * (49152 : ℝ) ^ (-σ) * c ^ p * t ^ (1 + σ)) *
        B ^ (u + ε) * δ ^ (s * (u + ε + 9 * p + 2 * σ + 2)) * bodyWeight σ w m l P n := by
  unfold bodyCellFactor bodyWeight
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow]
  ring

end WangZahlLot.Obl.wz_flat_factored_improvement
