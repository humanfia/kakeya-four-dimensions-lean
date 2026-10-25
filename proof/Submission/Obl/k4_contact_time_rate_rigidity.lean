import Mathlib
import ChallengeDeps
import Submission.Obl.k4_contact_time_rate_rigidity.Nested
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.TrueSystem
set_option linter.unusedVariables false

/-!
# `Submission.k4_contact_time_rate_rigidity`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_contact_time_rate_rigidity`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_contact_time_rate_rigidity/`
belong to this obligation.
-/

namespace Submission.Obl.k4_contact_time_rate_rigidity

open MeasureTheory Set Filter
open scoped ENNReal

theorem _root_.Submission.k4_contact_time_rate_rigidity : (((fun (horizontal:Bool) (regime:ℝ → Prop) => ∀ (N K:ℕ → ℝ),(∀ k,2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k,1 ≤ K k) ∧ ∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,K k ≤ N k ^ ε) → ∀ d κ ℓ S U e₀:ℝ,0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < ℓ → κ ≤ ℓ → 0 < S → S ≤ 1 → 0 < U → 0 < e₀ → regime κ → (horizontal = true → ℓ = κ) → ∀ (α:Type) [MeasurableSpace α] (ν:ℕ → MeasureTheory.Measure α) (μ ρ:ℕ → MeasureTheory.Measure (α × ℝ)) (π:ℕ → MeasureTheory.Measure ℝ) (b:ℕ → α → Fin 6 → ℝ) (P:ℕ → MvPolynomial (Fin 4) ℝ) (T n:ℕ → ℝ → ℕ) (j:(k:ℕ) → (s:ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A B:(k:ℕ) → (s:ℝ) → Fin (n k s) → Set α) (c:(k:ℕ) → (s:ℝ) → Fin (n k s) → Fin 5 → ℝ) (F:(k:ℕ) → (s:ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ),(∀ k,∀ᵐ p ∂μ k,|b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) → (fun (x:ℕ → α → ℝ → Fin 4 → ℝ) (I:(T:ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z:ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ => (fun fit:ℕ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → α → Set ℝ → Prop => (∀ k,Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0:ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k,|b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k,(∀ t ∈ Set.Icc (0:ℝ) 1,|MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3:Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (P k))|)) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ r s v:ℝ,R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a:ℤ,π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h:Bool,∀ (q:Fin 3 → ℤ) (a:ℤ),μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h:Bool,∀ (q:Fin 3 → ℤ) (a v₀:ℤ),μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ s:ℝ,R⁻¹ ≤ s → s ≤ U → (fun (q:ℝ) (a g:ℝ → ℝ) => N k ^ (κ * s) / K k ≤ (2:ℝ) ^ T k s ∧ (2:ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i,MeasurableSet (A k s i) ∧ MeasurableSet (B k s i) ∧ B k s i ⊆ A k s i) ∧ (∀ i i',i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i,ENNReal.ofReal (a s ^ d * q ^ 2 * g s / K k) ≤ ν k (A k s i) ∧ ν k (A k s i) ≤ ENNReal.ofReal (K k * a s ^ d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / K k) * ν k (A k s i) ≤ μ k (B k s i ×ˢ I (T k s) (j k s i)) ∧ (∀ e,|c k s i e| ≤ K k) ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ A k s i,∀ t ∈ I (T k s) (j k s i),|(x k l t) 1 - c k s i 0 - t * c k s i 1| ≤ K k * q ∧ |(x k l t) 2 - c k s i 2 - t * c k s i 3 - c k s i 4 * (x k l t) 1| ≤ K k * q * g s ∧ |b k l 4 - c k s i 3 - c k s i 4 * b k l 3| ≤ K k * g s) ∧ (∀ l ∈ B k s i,fit k (K k) (a s) (F k s i) l (I (T k s) (j k s i))) ∧ (∀ᵐ p ∂μ k,p.1 ∈ B k s i → p.2 ∈ I (T k s) (j k s i) → (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (F k s i))|) ∧ (horizontal = true → P k = MvPolynomial.X (3:Fin 4) ∧ (∀ᵐ p ∂μ k,|b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) ∧ |c k s i 3 + c k s i 0 + ((j k s i:ℕ) + (1:ℝ) / 2) * q * c k s i 1| + |c k s i 4 - ((j k s i:ℕ) + (1:ℝ) / 2) * q| ≤ K k * q ∧ (∃ L:Fin 4 → ℝ,F k s i = MvPolynomial.X (3:Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0:Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1:Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2:Fin 4)) ∧ |L 3| ≤ K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ B k s i,∀ t ∈ I (T k s) (j k s i),|L 1 - (x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂μ k,∃ i,p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i)) ∧ (∀ (i:Fin (n k s)) (v:ℝ) (v₀:ℤ),R⁻¹ ≤ v → v ≤ R → μ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * q) * ν k (A k s i) * π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) ((2:ℝ) ^ (-(T k s:ℤ))) (fun s => N k ^ (-s)) (fun s => N k ^ (-ℓ * s))) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ s t:ℝ,R⁻¹ ≤ s → s < t → t ≤ U → ∀ i:Fin (n k t),∃ h:Fin (n k s),A k t i ⊆ A k s h ∧ I (T k t) (j k t i) ⊆ I (T k s) (j k s h)) → ℓ ≤ κ) (fun k H a Q l I => ∀ t ∈ I,|MvPolynomial.eval (x k l t) Q| ≤ H * a ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3:Fin 4) Q)| ≤ H ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) Q))| ≤ H / a)) (fun k Nk r p e => ⌊(![p.2,(x k p.1 p.2) 1,(x k p.1 p.2) 2]:Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun k l t => ![t,b k l 0 + t * b k l 3,b k l 1 + t * b k l 4,b k l 2 + t * b k l 5]) (fun T j => Set.Icc (((j:ℕ):ℝ) / (2:ℝ) ^ T) ((((j:ℕ):ℝ) + 1) / (2:ℝ) ^ T)))) false (fun _ => True)) := by
  classical
  intro N K hN hNt hK d κ ℓ S U e₀ hd₀ hd₁ hκ₀ hκ₁ hℓ₀ hκℓ hS₀ hS₁ hU he₀
    _ _ α _ ν μ ρ π b P T n j A B c F hcontact hdata hcaps hlabels hnested
  simp only [zpow_neg, zpow_natCast] at hlabels
  by_contra hbad
  have hgap : κ < ℓ := lt_of_not_ge hbad
  have hN₁ (k : ℕ) : 1 ≤ N k := by linarith [hN k]
  let s : ℝ := min (U / 2) (min (e₀ / (2 * ℓ)) (κ * U / (2 * ℓ)))
  have hs : 0 < s := by dsimp [s]; positivity
  have hsU : s < U := (min_le_left _ _).trans_lt (by linarith)
  have hse : ℓ * s ≤ e₀ := by
    have hh : s ≤ e₀ / (2 * ℓ) := (min_le_right _ _).trans (min_le_left _ _)
    have := (le_div_iff₀ (show 0 < 2 * ℓ by positivity)).mp hh
    nlinarith
  have hst : ℓ * s ≤ κ * U := by
    have hh : s ≤ κ * U / (2 * ℓ) := (min_le_right _ _).trans (min_le_right _ _)
    have := (le_div_iff₀ (show 0 < 2 * ℓ by positivity)).mp hh
    nlinarith
  let v : ℝ := (ℓ - κ) * s / 2
  have hv : 0 < v := by dsimp [v]; positivity
  let R : ℝ := 2 + U + v + s⁻¹ + v⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
  have hR₀ : 0 < R := by linarith
  have hsR : R⁻¹ ≤ s := by
    have hh : s⁻¹ ≤ R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hs) hh
  have hvR : R⁻¹ ≤ v := by
    have hh : v⁻¹ ≤ R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hv) hh
  have hvR' : v ≤ R := by dsimp [R]; linarith [inv_pos.mpr hs, inv_pos.mpr hv]
  have hR₁ : R⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hR.le
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN₁ hNt hK.1 hK.2 3 (a := -S * v) (b := 0) (by nlinarith) (A := 6) (by norm_num)
  have hdecay := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN₁ hNt hK.1 hK.2 5 (a := κ * s - ℓ * s + v) (b := 0)
    (by dsimp [v]; nlinarith) (A := 14) (by norm_num)
  simp only [Real.rpow_zero] at hsmall hdecay
  suffices hfalse : ∀ᶠ k : ℕ in atTop, False by
    obtain ⟨_, hh⟩ := hfalse.exists
    exact hh
  filter_upwards [hcaps R hR, hlabels R hR, hnested R hR, hsmall, hdecay] with
    k hcapk hlabk hnestk hsmallk hdecayk
  have hNk : 0 < N k := by linarith [hN k]
  have hKk : 0 < K k := by linarith [hK.1 k]
  obtain ⟨hb, hν, hπ, hdom, hρ, hunit, hρmass, hP, hbnd, hPgood⟩ := hdata k
  letI : IsProbabilityMeasure (ν k) := hν
  obtain ⟨hTClo, hTCup, hAC, hdisj, hlabelC, hcoverC, hpalC⟩ := hlabk s hsR hsU.le
  obtain ⟨hTFlo, hTFup, hAF, hdisjF, hlabelF, hcoverF, hpalF⟩ :=
    hlabk U (hsR.trans hsU.le) le_rfl
  have hπcap := (hcapk 1 0 v hR₁ hR.le (by norm_num) (by linarith) hvR hvR').1
  let I := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block
  let q : ℝ := ((2 : ℝ) ^ T k U)⁻¹
  let g : ℝ := N k ^ (-ℓ * s)
  let δ : ℝ := N k ^ (-v)
  have hq : 0 < q := by dsimp [q]; positivity
  have hg : 0 < g := Real.rpow_pos_of_pos hNk _
  have hδ : 0 < δ := Real.rpow_pos_of_pos hNk _
  have hδ₁ : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN₁ k) (by linarith)
  have hblock (a : ℕ) (z : Fin (2 ^ a)) :
      I a z = Icc ((z : ℕ) / (2 : ℝ) ^ a)
        ((z : ℕ) / (2 : ℝ) ^ a + ((2 : ℝ) ^ a)⁻¹) := by
    simpa only [one_div] using
      Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_eq a z
  have hleft (a : ℕ) (z : Fin (2 ^ a)) :
      ((z : ℕ) / (2 : ℝ) ^ a) ∈ I a z := by
    rw [hblock]
    exact ⟨le_rfl, le_add_of_nonneg_right (by positivity)⟩
  have hqbound : q ≤ K k * g := by
    have hh := one_div_le_one_div_of_le
      (div_pos (Real.rpow_pos_of_pos hNk (κ * U)) hKk) hTFlo
    have hq' : q ≤ K k * N k ^ (-(κ * U)) := by
      rw [one_div_div] at hh
      simpa only [one_div, Real.rpow_neg hNk.le, div_eq_mul_inv, one_mul] using hh
    apply hq'.trans
    apply mul_le_mul_of_nonneg_left _ hKk.le
    exact Real.rpow_le_rpow_of_exponent_le (hN₁ k) (by nlinarith)
  have he : N k ^ (-e₀) ≤ g :=
    Real.rpow_le_rpow_of_exponent_le (hN₁ k) (by nlinarith)
  have hpos (i : Fin (n k U)) : ν k (A k U i) ≠ 0 := by
    have hpositive : 0 < ENNReal.ofReal
        ((N k ^ (-U)) ^ d * q ^ 2 * N k ^ (-ℓ * U) / K k) := by
      apply ENNReal.ofReal_pos.mpr
      positivity
    exact ne_of_gt (hpositive.trans_le (hlabelF i).1)
  have hbound := nested_time_bound (ν k) (μ k) (b k) (A k s) (j k s) (c k s)
    (A k U) (B k U) (fun i => I (T k U) (j k U i))
    (fun i => ((j k U i : ℕ) : ℝ) / (2 : ℝ) ^ T k U) (c k U)
    (K := K k) (q := q) (g := g) (e := N k ^ (-e₀)) (δ := δ)
    (η := N k ^ (-S * v)) (hK.1 k) hq hδ (by positivity) hdom
    (fun i => (hAC i).1) hdisj (fun i => (hAF i).2.2)
    (by
      intro i
      obtain ⟨h, ha, _⟩ := hnestk s U hsR hsU le_rfl i
      exact ⟨h, ha⟩)
    (by
      intro i l hl
      obtain ⟨_, _, _, _, _, hrow, _, _, _⟩ := hlabelC i
      exact (hrow l hl _ (hleft _ _)).2.2)
    (by
      intro i l hl
      obtain ⟨_, _, _, _, _, hrow, _, _, _⟩ := hlabelF i
      exact (hrow l hl _ (hleft _ _)).1)
    (by
      intro i t ht
      rw [hblock] at ht
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      dsimp [q]
      linarith [ht.2])
    (hcontact k) hpos (fun i => (hlabelF i).2.2.1)
    (by
      intro i a
      apply (hpalF i v a hvR hvR').trans
      gcongr
      exact hπcap a)
    hsmallk hcoverF
  have hτ := time_radius_le (hK.1 k) hq.le hg.le hδ hδ₁ hqbound he
  have hM : ((2 ^ T k s : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (K k * N k ^ (κ * s)) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast hTCup
  have hmass : ENNReal.ofReal ((K k)⁻¹) ≤
      ENNReal.ofReal (14 * K k ^ 4 * N k ^ (κ * s) * g / δ) := by
    calc
      _ ≤ μ k univ := hρmass.trans (hρ univ)
      _ ≤ _ := hbound
      _ ≤ ENNReal.ofReal (2 * K k * (7 * K k ^ 2 * g / δ)) *
          ENNReal.ofReal (K k * N k ^ (κ * s)) := by
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hreal : (K k)⁻¹ ≤ 14 * K k ^ 4 * N k ^ (κ * s) * g / δ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmass
  have hpower : N k ^ (κ * s) * g / δ = N k ^ (κ * s - ℓ * s + v) := by
    dsimp [g, δ]
    rw [← Real.rpow_add hNk, ← Real.rpow_sub hNk]
    congr 1
    ring
  have hlarge : 1 ≤ 14 * K k ^ 5 * N k ^ (κ * s - ℓ * s + v) := by
    calc
      1 = K k * (K k)⁻¹ := (mul_inv_cancel₀ hKk.ne').symm
      _ ≤ K k * (14 * K k ^ 4 * N k ^ (κ * s) * g / δ) :=
        mul_le_mul_of_nonneg_left hreal hKk.le
      _ = 14 * K k ^ 5 * (N k ^ (κ * s) * g / δ) := by ring
      _ = _ := by rw [hpower]
  exact hdecayk.not_ge hlarge

end Submission.Obl.k4_contact_time_rate_rigidity
