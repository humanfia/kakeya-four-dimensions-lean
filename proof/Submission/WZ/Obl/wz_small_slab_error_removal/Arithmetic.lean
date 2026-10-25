-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_slab_error_removal.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_slab_error_removal.Basic

namespace WangZahlLot.Obl.wz_small_slab_error_removal

/-- Separate the powers of the four geometric parameters. -/
theorem coefficient_factorization {s w ε a δ m l N : ℝ}
    (hδ : 0 < δ) (hm : 0 < m) (hl : 0 < l) (hN : 0 < N) :
    coefficient s w ε a δ m l N =
      a * δ ^ (w + ε + 2 - s) * m ^ (-1 + (3 / 2 : ℝ) * s) *
        l ^ (-s) * N ^ (1 - s) := by
  have hm_eq : m⁻¹ * (m ^ (-(3 / 2 : ℝ))) ^ (-s) =
      m ^ (-1 + (3 / 2 : ℝ) * s) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hm.le, ← Real.rpow_add hm]
    congr 1
    ring
  have hN_eq : N * N ^ (-s) = N ^ (1 - s) := by
    rw [sub_eq_add_neg, Real.rpow_add hN, Real.rpow_one]
  have hδ_eq : δ ^ (w + ε) * δ ^ 2 * δ ^ (-s) = δ ^ (w + ε + 2 - s) := by
    rw [← Real.rpow_two, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    rfl
  unfold coefficient
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hl.le, Real.mul_rpow hN.le hδ.le]
  calc
    _ = a * (δ ^ (w + ε) * δ ^ 2 * δ ^ (-s)) *
        (m⁻¹ * (m ^ (-(3 / 2 : ℝ))) ^ (-s)) * l ^ (-s) * (N * N ^ (-s)) := by ring
    _ = _ := by rw [hm_eq, hN_eq, hδ_eq]

theorem coefficient_antitone_convex {s w ε a δ m m' l N : ℝ}
    (hs : s ≤ (2 / 3 : ℝ)) (ha : 0 ≤ a) (hδ : 0 < δ)
    (hm : 0 < m) (hmm : m ≤ m') (hl : 0 < l) (hN : 0 < N) :
    coefficient s w ε a δ m' l N ≤ coefficient s w ε a δ m l N := by
  rw [coefficient_factorization hδ (hm.trans_le hmm) hl hN,
    coefficient_factorization hδ hm hl hN]
  have hpow : m' ^ (-1 + (3 / 2 : ℝ) * s) ≤ m ^ (-1 + (3 / 2 : ℝ) * s) :=
    Real.rpow_le_rpow_of_nonpos hm hmm (by linarith)
  gcongr

/-- On a compact range of radii only a uniform cardinality bound is needed. -/
theorem coefficient_le_card {s w ε a δ m l N : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hs23 : s ≤ (2 / 3 : ℝ))
    (hw : 0 ≤ w + ε) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 1 ≤ m) (hl : 1 ≤ l) (hN : 1 ≤ N) :
    coefficient s w ε a δ m l N ≤ a * N := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hl0 : 0 < l := zero_lt_one.trans_le hl
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  rw [coefficient_factorization hδ hm0 hl0 hN0]
  have hδp : δ ^ (w + ε + 2 - s) ≤ 1 :=
    Real.rpow_le_one hδ.le hδ1 (by linarith)
  have hmp : m ^ (-1 + (3 / 2 : ℝ) * s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm (by linarith)
  have hlp : l ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hl (by linarith)
  have hNp : N ^ (1 - s) ≤ N := by
    calc
      _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = N := Real.rpow_one _
  calc
    _ ≤ a * 1 * 1 * 1 * N := by gcongr
    _ = _ := by ring

/-- The powers in the desired slab estimate are exactly those obtained from
`q` copies after dividing their union bound by `q`. -/
theorem coefficient_replication_bound {s w ε a δ m l N m' q N' ζ : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ (1 / 2 : ℝ)) (hε : 0 < ε)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 < m) (hl : 0 < l) (hN : 0 < N)
    (hm' : 0 < m') (hq : 0 < q) (hN' : 0 < N')
    (hζ : 0 ≤ ζ) (hζε : 2 * ζ ≤ ε / 2)
    (hconvex : m' ≤ δ ^ (-ζ) * m)
    (hcopies : q ≤ δ ^ (-ζ) * l)
    (hcard : δ ^ ζ * q * N ≤ N') :
    q * coefficient s w ε a δ m l N ≤
      coefficient s w (ε / 2) a δ m' 1 N' := by
  let α : ℝ := -1 + (3 / 2 : ℝ) * s
  have hα : α ≤ 0 := by dsimp [α]; linarith
  have hNs : 0 ≤ 1 - s := by linarith
  have hc : (δ ^ (-ζ) * m) ^ α ≤ m' ^ α :=
    Real.rpow_le_rpow_of_nonpos hm' hconvex hα
  have hn : (δ ^ ζ * q * N) ^ (1 - s) ≤ N' ^ (1 - s) :=
    Real.rpow_le_rpow (by positivity) hcard hNs
  have hqpow : (δ ^ (-ζ) * l) ^ (-s) ≤ q ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hq hcopies (by linarith)
  have hqeq : q ^ (1 - s) = q * q ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add hq, Real.rpow_one]
  have hc' : δ ^ (-ζ * α) * m ^ α ≤ m' ^ α := by
    simpa only [Real.mul_rpow (Real.rpow_nonneg hδ.le _) hm.le,
      ← Real.rpow_mul hδ.le] using hc
  have hn' : δ ^ (ζ * (1 - s)) * q * q ^ (-s) * N ^ (1 - s) ≤ N' ^ (1 - s) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ δ ^ ζ * q) hN.le,
      Real.mul_rpow (Real.rpow_nonneg hδ.le _) hq.le, ← Real.rpow_mul hδ.le,
      hqeq] at hn
    simpa only [mul_assoc] using hn
  have hq' : δ ^ (ζ * s) * l ^ (-s) ≤ q ^ (-s) := by
    simpa only [Real.mul_rpow (Real.rpow_nonneg hδ.le _) hl.le,
      ← Real.rpow_mul hδ.le, neg_mul_neg] using hqpow
  have htotal : w + ε / 2 + 2 - s + -ζ * α + ζ * (1 - s) + ζ * s ≤
      w + ε + 2 - s := by
    have hζs : 0 ≤ ζ * ((3 / 2 : ℝ) * s) := by positivity
    dsimp [α] at *
    nlinarith
  have hscale := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 htotal
  rw [coefficient_factorization hδ hm hl hN,
    coefficient_factorization hδ hm' zero_lt_one hN', Real.one_rpow, mul_one]
  change q * (a * δ ^ (w + ε + 2 - s) * m ^ α * l ^ (-s) * N ^ (1 - s)) ≤ _
  calc
    _ ≤ q * (a * δ ^ (w + ε / 2 + 2 - s + -ζ * α + ζ * (1 - s) + ζ * s) *
        m ^ α * l ^ (-s) * N ^ (1 - s)) := by gcongr
    _ = a * δ ^ (w + ε / 2 + 2 - s) * (δ ^ (-ζ * α) * m ^ α) *
        (δ ^ (ζ * (1 - s)) * q * (δ ^ (ζ * s) * l ^ (-s)) * N ^ (1 - s)) := by
      simp only [Real.rpow_add hδ]
      ring
    _ ≤ a * δ ^ (w + ε / 2 + 2 - s) * (m' ^ α) * N' ^ (1 - s) := by
      apply mul_le_mul
      · gcongr
      · exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq' (by positivity)) (by positivity)).trans hn'
      · positivity
      · positivity

end WangZahlLot.Obl.wz_small_slab_error_removal
