import Mathlib

namespace Submission.Obl.k4_narrow_projected_row_parents

/-- The numerical common-frame conditions at one index, including the exact
natural time scale used by the sequence comparison. -/
structure CommonScaleChoice (Q β g χ ρ R : ℝ) where
  q : ℝ
  m : ℝ
  q_pos : 0 < q
  q_le_one : q ≤ 1
  q_parent : q ≤ Q
  m_pos : 0 < m
  m_le_q : m ≤ q
  area : q * g = m
  m_beta : m ≤ β
  major_parent : χ ≤ Q
  major_area : χ ≤ Q * g
  minor_area : m ≤ Q * g
  q_small : q ≤ ρ * Q / 10000
  major_small : χ ≤ ρ * (Q * g) / 10000
  minor_small : m ≤ ρ * (Q * g) / 10000
  major_minor : χ ≤ g
  major_one : χ ≤ 1
  natural_time : min Q (β / g) = R * q
  natural_area : min (Q * g) β = R * m

/-- A subpower divisor of the natural time scale satisfies the true and
projected frame requirements simultaneously. The refined major width only
needs its natural upper bound. -/
theorem natural_common_scales {Q β g χ ρ R a oldχ : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hβ : 0 < β) (hg : 0 < g) (hg1 : g ≤ 1)
    (hR : 1 ≤ R) (hstable : 10000 ≤ R * ρ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hχ : χ ≤ min oldχ (a * Q * g) / R) :
    Nonempty (CommonScaleChoice Q β g χ ρ R) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hnatural : 0 < min Q (β / g) := lt_min hQ (div_pos hβ hg)
  let q : ℝ := min Q (β / g) / R
  let m : ℝ := q * g
  have hq : 0 < q := div_pos hnatural hR0
  have hm : 0 < m := mul_pos hq hg
  have hqQ : q ≤ Q / R := div_le_div_of_nonneg_right (min_le_left _ _) hR0.le
  have hqβ : q ≤ (β / g) / R := div_le_div_of_nonneg_right (min_le_right _ _) hR0.le
  have hqQ' : q ≤ Q := hqQ.trans (div_le_self hQ.le hR)
  have hqβ' : q ≤ β / g := hqβ.trans (div_le_self (div_pos hβ hg).le hR)
  have hχQ : χ ≤ (Q * g) / R := by
    calc χ ≤ min oldχ (a * Q * g) / R := hχ
         _ ≤ (a * Q * g) / R := div_le_div_of_nonneg_right (min_le_right _ _) hR0.le
         _ ≤ (Q * g) / R := by
           gcongr
           exact mul_le_of_le_one_left hQ.le ha1
  have hχQg : χ ≤ Q * g := hχQ.trans (div_le_self (mul_pos hQ hg).le hR)
  have hχg : χ ≤ g := hχQg.trans (by nlinarith)
  have hfactor : 1 / R ≤ ρ / 10000 := by
    rw [div_le_div_iff₀ hR0 (by norm_num : (0 : ℝ) < 10000)]
    simpa only [one_mul, mul_comm] using hstable
  have hsmall {x : ℝ} (hx : 0 ≤ x) : x / R ≤ ρ * x / 10000 := by
    calc x / R = x * (1 / R) := by ring
         _ ≤ x * (ρ / 10000) := mul_le_mul_of_nonneg_left hfactor hx
         _ = _ := by ring
  refine ⟨{
    q := q
    m := m
    q_pos := hq
    q_le_one := hqQ'.trans hQ1
    q_parent := hqQ'
    m_pos := hm
    m_le_q := mul_le_of_le_one_right hq.le hg1
    area := rfl
    m_beta := (le_div_iff₀ hg).mp hqβ'
    major_parent := hχQg.trans (by nlinarith)
    major_area := hχQg
    minor_area := mul_le_mul_of_nonneg_right hqQ' hg.le
    q_small := hqQ.trans (hsmall hQ.le)
    major_small := hχQ.trans (hsmall (mul_pos hQ hg).le)
    minor_small := ?_
    major_minor := hχg
    major_one := hχg.trans hg1
    natural_time := ?_
    natural_area := ?_ }⟩
  · calc m = q * g := rfl
         _ ≤ (Q / R) * g := mul_le_mul_of_nonneg_right hqQ hg.le
         _ = (Q * g) / R := by ring
         _ ≤ _ := hsmall (mul_pos hQ hg).le
  · dsimp [q]
    field_simp
  · have hmin : min Q (β / g) * g = min (Q * g) β := by
      rw [min_mul_of_nonneg _ _ hg.le, div_mul_cancel₀ _ hg.ne']
    rw [← hmin]
    dsimp [m, q]
    field_simp

end Submission.Obl.k4_narrow_projected_row_parents
