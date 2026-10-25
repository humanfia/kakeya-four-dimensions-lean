import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Crossing

/-!
# From slice mass to a sublevel set of large measure

If a set of points of mass at least `M` has heights in `[z, z + H]`, each sub-interval
`⌊y / h⌋ = k` carries mass at most `c`, and every point's height lies within `E₀` of a slab
level for the law `g`, then the `E₀ + G' h` sublevel set of `g` around the levels has measure
at least `(M / c) h`. Combined with the crossing estimate this bounds the oscillation of `g`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

theorem floor_cell_subset {h y : ℝ} (hh : 0 < h) :
    Ico ((⌊y / h⌋ : ℝ) * h) (((⌊y / h⌋ : ℝ) + 1) * h) ⊆ Icc (y - h) (y + h) := by
  intro y' hy'
  have h1 := Int.floor_le (y / h)
  have h2 := Int.lt_floor_add_one (y / h)
  have h3 : (⌊y / h⌋ : ℝ) * h ≤ y := by rwa [le_div_iff₀ hh] at h1
  have h4 : y < ((⌊y / h⌋ : ℝ) + 1) * h := by rwa [div_lt_iff₀ hh] at h2
  constructor <;> nlinarith [hy'.1, hy'.2]

theorem mem_floor_cell {h y : ℝ} (hh : 0 < h) :
    y ∈ Ico ((⌊y / h⌋ : ℝ) * h) (((⌊y / h⌋ : ℝ) + 1) * h) := by
  have h1 := Int.floor_le (y / h)
  have h2 := Int.lt_floor_add_one (y / h)
  exact ⟨by rwa [le_div_iff₀ hh] at h1, by rwa [div_lt_iff₀ hh] at h2⟩

/-- Abstract mass-to-volume counting. -/
theorem volume_sublevel_of_mass {X : Type*} [MeasurableSpace X] (m : Measure X) (E : Set X)
    (y : X → ℝ) (g : ℝ → ℝ) (J : Finset ℝ) {z H h E₀ G' Mlo c : ℝ} (hh : 0 < h)
    (hc : 0 < c) (hG' : 0 ≤ G')
    (hEy : ∀ p ∈ E, y p ∈ Icc z (z + H))
    (hElev : ∀ p ∈ E, ∃ ℓ ∈ J, |g (y p) - ℓ| ≤ E₀)
    (hglip : ∀ u ∈ Icc (z - 2 * h) (z + H + 2 * h), ∀ u' ∈ Icc (z - 2 * h) (z + H + 2 * h),
      |g u - g u'| ≤ G' * |u - u'|)
    (hmass : ENNReal.ofReal Mlo ≤ m E)
    (hcube : ∀ k : ℤ, m (E ∩ {p | ⌊y p / h⌋ = k}) ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (Mlo / c * h) ≤
      volume {u : ℝ | u ∈ Icc (z - h) (z + H + h) ∧ ∃ ℓ ∈ J, |g u - ℓ| ≤ E₀ + G' * h} := by
  classical
  -- the finite set of occupied sub-cells
  set lo : ℤ := ⌊z / h⌋ with hlo
  set hi : ℤ := ⌊(z + H) / h⌋ with hhi
  set Ks : Finset ℤ := (Finset.Icc lo hi).filter (fun k => (E ∩ {p | ⌊y p / h⌋ = k}).Nonempty)
  have hcover : E ⊆ ⋃ k ∈ Ks, E ∩ {p | ⌊y p / h⌋ = k} := by
    intro p hp
    refine Set.mem_biUnion (x := ⌊y p / h⌋) (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩, ⟨p, hp, rfl⟩⟩) ⟨hp, rfl⟩
    · exact div_le_div_of_nonneg_right (hEy p hp).1 hh.le
    · exact div_le_div_of_nonneg_right (hEy p hp).2 hh.le
  have hmassK : m E ≤ (Ks.card : ℝ≥0∞) * ENNReal.ofReal c := by
    calc m E ≤ m (⋃ k ∈ Ks, E ∩ {p | ⌊y p / h⌋ = k}) := measure_mono hcover
      _ ≤ ∑ k ∈ Ks, m (E ∩ {p | ⌊y p / h⌋ = k}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ Ks, ENNReal.ofReal c := Finset.sum_le_sum (fun k _ => hcube k)
      _ = (Ks.card : ℝ≥0∞) * ENNReal.ofReal c := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : Mlo / c ≤ (Ks.card : ℝ) := by
    have h1 := hmass.trans hmassK
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at h1
    rcases le_or_gt Mlo 0 with hM | hM
    · exact (div_nonpos_of_nonpos_of_nonneg hM hc.le).trans (by positivity)
    · have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
      rw [div_le_iff₀ hc]; exact this
  -- each occupied sub-cell lies in the sublevel set
  have hsub : ⋃ k ∈ Ks, Ico ((k : ℝ) * h) (((k : ℝ) + 1) * h) ⊆
      {u : ℝ | u ∈ Icc (z - h) (z + H + h) ∧ ∃ ℓ ∈ J, |g u - ℓ| ≤ E₀ + G' * h} := by
    intro u hu
    obtain ⟨k, hk, hu⟩ := Set.mem_iUnion₂.mp hu
    obtain ⟨_, ⟨p, hpE, hpk⟩⟩ := Finset.mem_filter.mp hk
    have hpk' : ⌊y p / h⌋ = k := hpk
    have hyz := hEy p hpE
    have hcell := floor_cell_subset (y := y p) hh
    rw [hpk'] at hcell
    have hu' := hcell hu
    obtain ⟨ℓ, hℓ, hℓp⟩ := hElev p hpE
    refine ⟨⟨by linarith [hu'.1, hyz.1], by linarith [hu'.2, hyz.2]⟩, ℓ, hℓ, ?_⟩
    have hdist : |u - y p| ≤ h := by
      have h1 := mem_floor_cell (y := y p) hh
      rw [hpk'] at h1
      rw [abs_le]; constructor <;> nlinarith [hu.1, hu.2, h1.1, h1.2]
    have hlip := hglip u ⟨by linarith [hu'.1, hyz.1], by linarith [hu'.2, hyz.2]⟩
      (y p) ⟨by linarith [hyz.1], by linarith [hyz.2]⟩
    calc |g u - ℓ| ≤ |g u - g (y p)| + |g (y p) - ℓ| := by
          have := abs_add_le (g u - g (y p)) (g (y p) - ℓ); simpa using this
      _ ≤ G' * |u - y p| + E₀ := add_le_add hlip hℓp
      _ ≤ G' * h + E₀ := by gcongr
      _ = E₀ + G' * h := by ring
  have hdisj : Set.PairwiseDisjoint (↑Ks : Set ℤ)
      (fun k : ℤ => Ico ((k : ℝ) * h) (((k : ℝ) + 1) * h)) := by
    intro k _ k' _ hkk'
    rw [Function.onFun, Set.disjoint_iff]
    intro u ⟨hu1, hu2⟩
    apply hkk'
    have a1 : (k : ℝ) < (k' : ℝ) + 1 := by
      have := lt_of_le_of_lt hu1.1 hu2.2
      nlinarith
    have a2 : (k' : ℝ) < (k : ℝ) + 1 := by
      have := lt_of_le_of_lt hu2.1 hu1.2
      nlinarith
    have b1 : k < k' + 1 := by exact_mod_cast a1
    have b2 : k' < k + 1 := by exact_mod_cast a2
    omega
  calc ENNReal.ofReal (Mlo / c * h) ≤ (Ks.card : ℝ≥0∞) * ENNReal.ofReal h := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hh.le)
    _ = ∑ k ∈ Ks, volume (Ico ((k : ℝ) * h) (((k : ℝ) + 1) * h)) := by
        have hvol : ∀ k : ℤ, volume (Ico ((k : ℝ) * h) (((k : ℝ) + 1) * h)) = ENNReal.ofReal h := by
          intro k; rw [Real.volume_Ico]; congr 1; ring
        rw [Finset.sum_congr rfl (fun k _ => hvol k), Finset.sum_const, nsmul_eq_mul]
    _ = volume (⋃ k ∈ Ks, Ico ((k : ℝ) * h) (((k : ℝ) + 1) * h)) := by
        rw [measure_biUnion_finset hdisj (fun k _ => measurableSet_Ico)]
    _ ≤ _ := measure_mono hsub

/-- Crossing, from mass: the quadratic law `A0 + A1 u + A2 u^2` is Lipschitz with constant
`14 B a₀ / (H + 2h)` on the triple-size neighbourhood of the cell. -/
theorem crossing_lipschitz {X : Type*} [MeasurableSpace X] (m : Measure X) (E : Set X)
    (y : X → ℝ) (A0 A1 A2 : ℝ) (J : Finset ℝ) {z H h E₀ G' Mlo c d a₀ Cs : ℝ}
    (hh : 0 < h) (hH : 0 < H) (hc : 0 < c) (hG' : 0 ≤ G') (hE₀ : 0 ≤ E₀) (hMlo : 0 < Mlo)
    (hd0 : 0 ≤ d) (hd1 : d < 1) (ha₀ : 0 < a₀) (hCs : 0 ≤ Cs)
    (hθ1 : Mlo / c * h ≤ H + 2 * h)
    (hEy : ∀ p ∈ E, y p ∈ Icc z (z + H))
    (hElev : ∀ p ∈ E, ∃ ℓ ∈ J, |(A0 + A1 * y p + A2 * y p ^ 2) - ℓ| ≤ E₀)
    (hglip : ∀ u ∈ Icc (z - 2 * h) (z + H + 2 * h), ∀ u' ∈ Icc (z - 2 * h) (z + H + 2 * h),
      |(A0 + A1 * u + A2 * u ^ 2) - (A0 + A1 * u' + A2 * u' ^ 2)| ≤ G' * |u - u'|)
    (hmass : ENNReal.ofReal Mlo ≤ m E)
    (hcube : ∀ k : ℤ, m (E ∩ {p | ⌊y p / h⌋ = k}) ≤ ENNReal.ofReal c)
    (hcount : ∀ w W : ℝ, a₀ ≤ W →
      ((J.filter (fun ℓ => w ≤ ℓ ∧ ℓ ≤ w + W)).card : ℝ) ≤ Cs * (W / a₀) ^ d) :
    ∀ u ∈ Icc (z - 3 * H) (z + 4 * H), ∀ u' ∈ Icc (z - 3 * H) (z + 4 * H),
      |(A0 + A1 * u + A2 * u ^ 2) - (A0 + A1 * u' + A2 * u' ^ 2)| ≤
        14 * (max 1 ((2 * ((E₀ + G' * h) / a₀) + 40 * ((E₀ + G' * h) / a₀) * Cs /
          (Mlo / c * h / (H + 2 * h)) ^ 2) ^ (1 / (1 - d)))) * a₀ / (H + 2 * h) * |u - u'| := by
  set g : ℝ → ℝ := fun u => A0 + A1 * u + A2 * u ^ 2 with hg
  set H'' := H + 2 * h with hH''
  have hH''pos : 0 < H'' := by positivity
  set cc := z + H / 2 with hcc
  have hvol := volume_sublevel_of_mass m E y g J hh hc hG' hEy hElev hglip hmass hcube
  set θ := Mlo / c * h / H'' with hθdef
  have hθpos : 0 < θ := by positivity
  have hθ1' : θ ≤ 1 := by rw [hθdef, div_le_one hH''pos]; exact hθ1
  set e := (E₀ + G' * h) / a₀ with hedef
  have he : 0 ≤ e := by positivity
  -- the law as a centered quadratic
  have hquad : ∀ u, g u = quad (g cc) (A1 + 2 * A2 * cc) A2 cc u := by
    intro u; simp only [hg, quad]; ring
  have hS : ENNReal.ofReal (θ * H'') ≤ volume {u : ℝ | u ∈ Icc (cc - H'' / 2) (cc + H'' / 2) ∧
      ∃ ℓ ∈ J, |quad (g cc) (A1 + 2 * A2 * cc) A2 cc u - ℓ| ≤ e * a₀} := by
    have h1 : θ * H'' = Mlo / c * h := by rw [hθdef]; field_simp
    have h2 : e * a₀ = E₀ + G' * h := by rw [hedef]; field_simp
    have h3 : Icc (cc - H'' / 2) (cc + H'' / 2) = Icc (z - h) (z + H + h) := by
      rw [hcc, hH'']; congr 1 <;> ring
    rw [h1, h2, h3]
    refine le_trans hvol (le_of_eq ?_)
    congr 1
    ext u
    simp only [mem_ofPred_eq, ← hquad]
  have hcross := crossing_osc_bound hd0 hd1 ha₀ he hH''pos hθpos hθ1' hCs (g cc)
    (A1 + 2 * A2 * cc) A2 cc J hcount hS
  set Bc := max 1 ((2 * e + 40 * e * Cs / θ ^ 2) ^ (1 / (1 - d))) with hBc
  intro u hu u' hu'
  have hdiff : g u - g u' = (u - u') * ((A1 + 2 * A2 * cc) + A2 * (u + u' - 2 * cc)) := by
    simp only [hg]; ring
  have hsum : |u + u' - 2 * cc| ≤ 7 * H'' := by
    rw [abs_le, hcc, hH'']; constructor <;> nlinarith [hu.1, hu.2, hu'.1, hu'.2]
  have hβγ : |A1 + 2 * A2 * cc| + |A2| * (7 * H'') ≤ 14 * Bc * a₀ / H'' := by
    rw [le_div_iff₀ hH''pos]
    nlinarith [abs_nonneg (A1 + 2 * A2 * cc), abs_nonneg A2]
  calc |g u - g u'| = |u - u'| * |(A1 + 2 * A2 * cc) + A2 * (u + u' - 2 * cc)| := by
        rw [hdiff, abs_mul]
    _ ≤ |u - u'| * (|A1 + 2 * A2 * cc| + |A2| * (7 * H'')) := by
        gcongr
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        gcongr
    _ ≤ |u - u'| * (14 * Bc * a₀ / H'') := by gcongr
    _ = 14 * Bc * a₀ / H'' * |u - u'| := by ring

/-- Crossing at one cell, from label densities and a d-dimensional window cap. -/
theorem crossing_point {X ι : Type*} [MeasurableSpace X] (m : Measure X)
    (S : Finset ι) (Eℓ : ι → Set X) (ℓ : ι → ℝ) (Es Ω : Set X)
    (y x3v : X → ℝ) (A0 A1 A2 : ℝ)
    {z H h Ea Eb G' Mlo c d a₀ θ₁ Ccap : ℝ}
    (hh : 0 < h) (hH : 0 < H) (hc : 0 < c) (hG' : 0 ≤ G') (hEa : 0 ≤ Ea) (hEb : 0 ≤ Eb)
    (hMlo : 0 < Mlo) (hd0 : 0 ≤ d) (hd1 : d < 1) (ha₀ : 0 < a₀) (hθ₁ : 0 < θ₁)
    (hCcap : 0 ≤ Ccap) (hθ1 : Mlo / c * h ≤ H + 2 * h)
    (hEsy : ∀ p ∈ Es, y p ∈ Icc z (z + H))
    (hEslab : ∀ p ∈ Es, ∃ j ∈ S, p ∈ Eℓ j)
    (hlablev : ∀ j ∈ S, ∀ p ∈ Eℓ j, |x3v p - ℓ j| ≤ Ea)
    (hEslaw : ∀ p ∈ Es, |x3v p - (A0 + A1 * y p + A2 * y p ^ 2)| ≤ Eb)
    (hglip : ∀ u ∈ Icc (z - 2 * h) (z + H + 2 * h), ∀ u' ∈ Icc (z - 2 * h) (z + H + 2 * h),
      |(A0 + A1 * u + A2 * u ^ 2) - (A0 + A1 * u' + A2 * u' ^ 2)| ≤ G' * |u - u'|)
    (hmass : ENNReal.ofReal Mlo ≤ m Es)
    (hcube : ∀ k : ℤ, m (Es ∩ {p | ⌊y p / h⌋ = k}) ≤ ENNReal.ofReal c)
    (hdense : ∀ j ∈ S, ENNReal.ofReal θ₁ ≤ m (Eℓ j))
    (hmeasEℓ : ∀ j ∈ S, MeasurableSet (Eℓ j))
    (hdisj : ∀ j ∈ S, ∀ j' ∈ S, j ≠ j' → Disjoint (Eℓ j) (Eℓ j'))
    (hΩ : ∀ j ∈ S, Eℓ j ⊆ Ω)
    (hcap : ∀ w W' : ℝ, a₀ ≤ W' → m (Ω ∩ {p | x3v p ∈ Icc w (w + W')}) ≤
      ENNReal.ofReal (Ccap * W' ^ d)) :
    ∀ u ∈ Icc (z - 3 * H) (z + 4 * H), ∀ u' ∈ Icc (z - 3 * H) (z + 4 * H),
      |(A0 + A1 * u + A2 * u ^ 2) - (A0 + A1 * u' + A2 * u' ^ 2)| ≤
        14 * (max 1 ((2 * ((Ea + Eb + G' * h) / a₀) + 40 * ((Ea + Eb + G' * h) / a₀) *
          (Ccap * (1 + 2 * Ea / a₀) ^ d * a₀ ^ d / θ₁) /
          (Mlo / c * h / (H + 2 * h)) ^ 2) ^ (1 / (1 - d)))) * a₀ / (H + 2 * h) * |u - u'| := by
  classical
  set J : Finset ℝ := S.image ℓ with hJ
  have hElev : ∀ p ∈ Es, ∃ l ∈ J, |(A0 + A1 * y p + A2 * y p ^ 2) - l| ≤ Ea + Eb := by
    intro p hp
    obtain ⟨j, hjS, hpj⟩ := hEslab p hp
    refine ⟨ℓ j, Finset.mem_image_of_mem ℓ hjS, ?_⟩
    have h1 := hlablev j hjS p hpj
    have h2 := hEslaw p hp
    calc |(A0 + A1 * y p + A2 * y p ^ 2) - ℓ j|
        ≤ |x3v p - (A0 + A1 * y p + A2 * y p ^ 2)| + |x3v p - ℓ j| := by
          have := abs_sub_le (A0 + A1 * y p + A2 * y p ^ 2) (x3v p) (ℓ j)
          rw [abs_sub_comm (A0 + A1 * y p + A2 * y p ^ 2) (x3v p)] at this; exact this
      _ ≤ Eb + Ea := add_le_add h2 h1
      _ = Ea + Eb := by ring
  have hCs0 : 0 ≤ Ccap * (1 + 2 * Ea / a₀) ^ d * a₀ ^ d / θ₁ := by positivity
  have hcount : ∀ w W : ℝ, a₀ ≤ W →
      ((J.filter (fun l => w ≤ l ∧ l ≤ w + W)).card : ℝ) ≤
        (Ccap * (1 + 2 * Ea / a₀) ^ d * a₀ ^ d / θ₁) * (W / a₀) ^ d := by
    intro w W hW
    set S' := S.filter (fun j => w ≤ ℓ j ∧ ℓ j ≤ w + W) with hS'
    have hcardJ : (J.filter (fun l => w ≤ l ∧ l ≤ w + W)).card ≤ S'.card := by
      rw [hJ, Finset.filter_image]
      exact Finset.card_image_le
    have hsub : (⋃ j ∈ S', Eℓ j) ⊆ Ω ∩ {p | x3v p ∈ Icc (w - Ea) (w - Ea + (W + 2 * Ea))} := by
      intro p hp
      obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.mp hp
      obtain ⟨hjS, hjw⟩ := Finset.mem_filter.mp hj
      have h1 := abs_le.mp (hlablev j hjS p hpj)
      exact ⟨hΩ j hjS hpj, by constructor <;> linarith [hjw.1, hjw.2, h1.1, h1.2]⟩
    have hW2 : a₀ ≤ W + 2 * Ea := by linarith
    have hsum : (S'.card : ℝ≥0∞) * ENNReal.ofReal θ₁ ≤ ENNReal.ofReal (Ccap * (W + 2 * Ea) ^ d) := by
      calc (S'.card : ℝ≥0∞) * ENNReal.ofReal θ₁ = ∑ _j ∈ S', ENNReal.ofReal θ₁ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ S', m (Eℓ j) := Finset.sum_le_sum (fun j hj =>
            hdense j (Finset.mem_filter.mp hj).1)
        _ = m (⋃ j ∈ S', Eℓ j) := by
            rw [measure_biUnion_finset]
            · intro j hj j' hj' hjj'
              exact hdisj j (Finset.mem_filter.mp hj).1 j' (Finset.mem_filter.mp hj').1 hjj'
            · intro j hj; exact hmeasEℓ j (Finset.mem_filter.mp hj).1
        _ ≤ m (Ω ∩ {p | x3v p ∈ Icc (w - Ea) (w - Ea + (W + 2 * Ea))}) := measure_mono hsub
        _ ≤ ENNReal.ofReal (Ccap * (W + 2 * Ea) ^ d) := hcap _ _ hW2
    have hreal : (S'.card : ℝ) * θ₁ ≤ Ccap * (W + 2 * Ea) ^ d := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hsum
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hCcap (Real.rpow_nonneg (by linarith) d))).mp hsum
    have hpow : (W + 2 * Ea) ^ d ≤ (1 + 2 * Ea / a₀) ^ d * a₀ ^ d * (W / a₀) ^ d := by
      have h1 : W + 2 * Ea ≤ (1 + 2 * Ea / a₀) * W := by
        have : 2 * Ea ≤ 2 * Ea / a₀ * W := by
          rw [div_mul_eq_mul_div, le_div_iff₀ ha₀]; nlinarith
        linarith
      calc (W + 2 * Ea) ^ d ≤ ((1 + 2 * Ea / a₀) * W) ^ d :=
            Real.rpow_le_rpow (by linarith) h1 hd0
        _ = (1 + 2 * Ea / a₀) ^ d * a₀ ^ d * (W / a₀) ^ d := by
            rw [Real.mul_rpow (by positivity) (by linarith), mul_assoc,
              ← Real.mul_rpow ha₀.le (div_nonneg (by linarith) ha₀.le)]
            congr 2; field_simp
    calc ((J.filter (fun l => w ≤ l ∧ l ≤ w + W)).card : ℝ) ≤ S'.card := by exact_mod_cast hcardJ
      _ ≤ Ccap * (W + 2 * Ea) ^ d / θ₁ := by rw [le_div_iff₀ hθ₁]; exact hreal
      _ ≤ Ccap * ((1 + 2 * Ea / a₀) ^ d * a₀ ^ d * (W / a₀) ^ d) / θ₁ := by
          gcongr
      _ = (Ccap * (1 + 2 * Ea / a₀) ^ d * a₀ ^ d / θ₁) * (W / a₀) ^ d := by ring
  have := crossing_lipschitz m Es y A0 A1 A2 J hh hH hc hG' (by positivity) hMlo hd0 hd1 ha₀ hCs0
    hθ1 hEsy hElev hglip hmass hcube hcount
  simpa [add_assoc] using this

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
