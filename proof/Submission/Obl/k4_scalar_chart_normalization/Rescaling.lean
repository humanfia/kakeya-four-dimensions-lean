import Submission.Obl.k4_scalar_chart_normalization.Defs

namespace Submission.Obl.k4_scalar_chart_normalization

open MeasureTheory Filter
open scoped ENNReal Topology

/-- Reindex all sample-dependent data, keeping the fixed exponents. -/
noncomputable def reindex (p : Problem) (φ : ℕ → ℕ) : Problem :=
  ⟨fun k => p.1 (φ k), (fun k => p.N (φ k)), (fun k => p.K (φ k)),
    p.M, p.D, p.L, p.d, p.S, p.U,
    (fun k => p.w (φ k)), (fun k => p.nu (φ k)), (fun k => p.E (φ k)),
    (fun k => p.rho (φ k)), (fun k => p.rhoA (φ k)), p.f⟩

/-- Change the reference resolution by a positive power. -/
noncomputable def powerScale (p : Problem) (α : ℝ) (M : ℕ) : Problem :=
  ⟨p.1, (fun k => p.N k ^ α), p.K, M, p.D, p.L / α, p.d, p.S, p.U / α,
    p.w, p.nu, p.E, (fun k a r => p.rho k a (α * r)),
    (fun k a u => p.rhoA k a (α * u)), (fun r => p.f (α * r) / α)⟩


private theorem powerScale_N (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).N = (fun k => p.N k ^ α) := rfl

private theorem powerScale_K (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).K = p.K := rfl

private theorem powerScale_M (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).M = M := rfl

private theorem powerScale_D (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).D = p.D := rfl

private theorem powerScale_L (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).L = p.L / α := rfl

private theorem powerScale_d (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).d = p.d := rfl

private theorem powerScale_S (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).S = p.S := rfl

private theorem powerScale_U (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).U = p.U / α := rfl

private theorem powerScale_w (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).w = p.w := rfl

private theorem powerScale_nu (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).nu = p.nu := rfl

private theorem powerScale_E (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).E = p.E := rfl

private theorem powerScale_rho (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).rho = (fun k a r => p.rho k a (α * r)) := rfl

private theorem powerScale_rhoA (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).rhoA = (fun k a u => p.rhoA k a (α * u)) := rfl

private theorem powerScale_f (p : Problem) (α : ℝ) (M : ℕ) :
    (powerScale p α M).f = (fun r => p.f (α * r) / α) := rfl

private theorem mu_powerScale (p : Problem) (α : ℝ) (M : ℕ) :
    mu (powerScale p α M) = mu p := rfl

/-- Polynomial sign descriptions remain valid when either budget grows. -/
theorem Format.mono {n : ℕ} {B B' : ℝ} {D D' : ℕ} {A : Set (Fin n → ℝ)}
    (h : Format n B D A) (hB : B ≤ B') (hD : D ≤ D') : Format n B' D' A := by
  obtain ⟨k, hk, p, hp, S, rfl⟩ := h
  exact ⟨k, hk.trans hB, p, fun i => ⟨(hp i).1.trans hD,
    fun a => ((hp i).2 a).trans hB⟩, S, rfl⟩

/-- All the exact-problem hypotheses pass to a cofinal reindexing. -/
theorem exact_reindex {p : Problem} (hp : Exact p) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) : Exact (reindex p φ) := by
  rcases hp with ⟨hbase, hworld, hdensity, hjoint, hprofile, htypical, hcap, hangular⟩
  rcases hbase with ⟨hN, hNt, hK, hM, hD, hL, hd, hd1, hS, hU⟩
  refine ⟨⟨fun k => hN (φ k), hNt.comp hφ,
    ⟨fun k => hK.1 (φ k), fun ε hε => hφ.eventually (hK.2 ε hε)⟩,
    hM, hD, hL, hd, hd1, hS, hU⟩,
    (fun k => hworld (φ k)), (fun k => hdensity (φ k)),
    (fun k => hjoint (φ k)), hprofile, ?_, hcap, ?_⟩
  · intro r τ hr hrL hτ
    obtain ⟨c, hc, he⟩ := htypical r τ hr hrL hτ
    exact ⟨c, hc, hφ.eventually he⟩
  · intro u τ hu huU hτ
    obtain ⟨c, hc, he⟩ := hangular u τ hu huU hτ
    exact ⟨c, hc, hφ.eventually he⟩

/-- Reindexing does not change the chart witnesses at a sample. -/
theorem chart_reindex (p : Problem) (φ : ℕ → ℕ) (B : ℕ)
    (r b h ε : ℝ) (truth : Bool) (k : ℕ) :
    Chart (reindex p φ) B r b h ε truth k ↔ Chart p B r b h ε truth (φ k) := by
  rfl

/-- Deleting a finite initial segment preserves every chart cost. -/
theorem cost_shift_iff (p : Problem) (m : ℕ) (h : ℝ) :
    Cost (reindex p (fun k => k + m)) h ↔ Cost p h := by
  change (0 ≤ h ∧ ∃ B, 1 ≤ B ∧ ∀ ε : ℝ, 0 < ε →
    ∃ᶠ k in atTop, Chart p B p.L p.L (h + ε) ε true (k + m)) ↔ _
  simp only [← frequently_map, map_add_atTop_eq_nat, Cost]


/-- Deleting a finite prefix preserves the horizon, including its definition by infimum. -/
theorem horizon_shift (p : Problem) (m : ℕ) :
    Horizon (reindex p (fun k => k + m)) = Horizon p := by
  unfold Horizon
  congr 1
  ext h
  exact cost_shift_iff p m h

private theorem scaled_power {N α z : ℝ} (hN : 0 ≤ N) :
    (N ^ α) ^ z = N ^ (α * z) := (Real.rpow_mul hN α z).symm

/-- Exact data remain exact after changing the reference power, provided the
new polynomial budget dominates the old one. -/
theorem exact_powerScale {p : Problem} (hp : Exact p) {α : ℝ} (hα : 0 < α)
    {M : ℕ} (hM : 1 ≤ M) (hbudget : (p.M : ℝ) ≤ α * (M : ℝ))
    (hscale : ∀ k, 2 ≤ p.N k ^ α) : Exact (powerScale p α M) := by
  rcases hp with ⟨hbase, hworld, hdensity, hjoint, hprofile, htypical, hcap, hangular⟩
  rcases hbase with ⟨hN, hNt, hK, hMold, hD, hL, hd, hd1, hS, hU⟩
  have hNpos (k : ℕ) : 0 < p.N k := by linarith [hN k]
  have hpower (k : ℕ) (z : ℝ) : (p.N k ^ α) ^ z = p.N k ^ (α * z) :=
    scaled_power (hNpos k).le
  have hlarge (k : ℕ) : p.N k ^ (p.M : ℝ) ≤ (p.N k ^ α) ^ (M : ℝ) := by
    rw [hpower]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [hN k]) hbudget
  have halpha : α ≠ 0 := hα.ne'
  refine ⟨⟨hscale, (tendsto_rpow_atTop hα).comp hNt,
    ⟨hK.1, ?_⟩, hM, hD, div_pos hL hα, hd, hd1, hS, div_pos hU hα⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    simpa only [powerScale_K, powerScale_N, hpower] using hK.2 (α * ε) (mul_pos hα hε)
  · intro k
    rcases hworld k with ⟨hW, hw, hsum, hprior, hmass⟩
    refine ⟨hW.trans (hlarge k), hw, hsum, ?_, hmass⟩
    intro a
    rcases hprior a with ⟨hprob, ⟨n, hn, h, i, A, hA, hnu⟩, hb, hE, hEsub, htag, hfmt⟩
    refine ⟨hprob, ⟨n, hn.trans (hlarge k), h, i, A, ?_, hnu⟩, hb, hE, hEsub,
      (fun z hz => (htag z hz).trans (hlarge k)), ?_⟩
    · intro j
      rcases hA j with ⟨hj0, hj, hij, hAj, hbAj⟩
      exact ⟨hj0, hj.trans (hlarge k), hij.trans (hlarge k),
        hAj.mono (hlarge k) le_rfl, fun b hb e => (hbAj b hb e).trans (hlarge k)⟩
    · intro i
      exact (hfmt i).mono (hlarge k) le_rfl
  · intro k a r hr hrL
    have hrL' : α * r ≤ p.L := by
      have := (le_div_iff₀ hα).mp hrL
      nlinarith
    obtain ⟨hm, heq⟩ := hdensity k a (α * r) (mul_nonneg hα.le hr) hrL'
    refine ⟨hm, ?_⟩
    simpa only [powerScale_N, powerScale_rho, mu_powerScale, hpower, mul_neg] using heq
  · intro k a u hu huU
    have huU' : α * u ≤ p.U := by
      have := (le_div_iff₀ hα).mp huU
      nlinarith
    obtain ⟨hm, heq⟩ := hjoint k a (α * u) (mul_pos hα hu) huU'
    refine ⟨hm, ?_⟩
    simpa only [powerScale_N, powerScale_L, powerScale_rhoA, mu_powerScale, hpower,
      mul_neg, mul_div_cancel₀ _ halpha] using heq
  · intro r s hr hrs hsL
    have hsL' : α * s ≤ p.L := by
      have := (le_div_iff₀ hα).mp hsL
      nlinarith
    obtain ⟨h0, h1⟩ := hprofile (α * r) (α * s) (mul_nonneg hα.le hr)
      (mul_le_mul_of_nonneg_left hrs hα.le) hsL'
    dsimp [powerScale, Problem.f]
    rw [← sub_div]
    exact ⟨div_nonneg h0 hα.le, (div_le_iff₀ hα).mpr (by nlinarith)⟩
  · intro r τ hr hrL hτ
    have hrL' : α * r ≤ p.L := by
      have := (le_div_iff₀ hα).mp hrL
      nlinarith
    obtain ⟨c, hc, he⟩ := htypical (α * r) (α * τ) (mul_nonneg hα.le hr)
      hrL' (mul_pos hα hτ)
    refine ⟨c / α, div_pos hc hα, ?_⟩
    have hlo : α * (-(p.f (α * r) / α) - τ) = -p.f (α * r) - α * τ := by
      field_simp
    have hhi : α * (-(p.f (α * r) / α) + τ) = -p.f (α * r) + α * τ := by
      field_simp
    have hc' : α * (-(c / α)) = -c := by field_simp
    simp only [powerScale_N, powerScale_f, powerScale_rho, powerScale_w, mu_powerScale,
      hpower, mul_neg, hlo, hhi, hc']
    convert he using 1
    rfl
  · intro r hr hrL
    have hrL' : α * r ≤ p.L := by
      have := (le_div_iff₀ hα).mp hrL
      nlinarith
    have hc := hcap (α * r) (mul_nonneg hα.le hr) hrL'
    dsimp [powerScale, Problem.f, Problem.L, Problem.d]
    have hcancel : α * (p.L / α) = p.L := mul_div_cancel₀ p.L halpha
    rw [hcancel, ← sub_div]
    apply (div_le_iff₀ hα).mpr
    nlinarith [hc]
  · intro u τ hu huU hτ
    have huU' : α * u ≤ p.U := by
      have := (le_div_iff₀ hα).mp huU
      nlinarith
    obtain ⟨c, hc, he⟩ := hangular (α * u) (α * τ) (mul_pos hα hu) huU'
      (mul_pos hα hτ)
    refine ⟨c / α, div_pos hc hα, ?_⟩
    have ht : α * (-(p.f p.L / α) - p.S * u + τ) =
        -p.f p.L - p.S * (α * u) + α * τ := by field_simp
    have hc' : α * (-(c / α)) = -c := by field_simp
    simp only [powerScale_N, powerScale_L, powerScale_S, powerScale_f, powerScale_rhoA,
      powerScale_w, mu_powerScale, hpower, mul_div_cancel₀ _ halpha, mul_neg, ht, hc']
    convert he using 1
    rfl


/-- Every old chart transports to the new reference power; its witnesses and
assigned priors are unchanged. Only the complexity budget may grow. -/
theorem chartData_powerScale {p : Problem} {α : ℝ} (hα : α ≠ 0) (M : ℕ)
    {B B' k T n : ℕ} {r b h ε : ℝ} {truth : Bool}
    {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hN : 1 ≤ p.N k) (hB : B ≤ B') (hBe : (B : ℝ) ≤ α * (B' : ℝ))
    (hc : ChartData p B (α * r) (α * b) (α * h) (α * ε) truth k
      T n γ j A C u v J P Λ) :
    ChartData (powerScale p α M) B' r b h ε truth k T n γ j A C u v J P Λ := by
  have hp (z : ℝ) : (p.N k ^ α) ^ z = p.N k ^ (α * z) := scaled_power (by linarith)
  have hb : p.N k ^ (B : ℝ) ≤ p.N k ^ (α * (B' : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN hBe
  simp only [ChartData, powerScale_N, powerScale_E, powerScale_w, powerScale_f,
    mu_powerScale, hp, mul_neg, mul_div_cancel₀ _ hα]
  rcases hc with ⟨ht, hn, hmeas, hdisj, hsub, hc, hlist, hlmeas, hcover, hmass⟩
  refine ⟨ht, hn.trans hb, hmeas, hdisj, hsub, ?_, hlist, hlmeas, hcover, hmass⟩
  intro i
  rcases hc i with ⟨hm, hJ, hJi, hJu, huv, hP, hcoeff, hbound, hA, hC, hfit, hfloor⟩
  exact ⟨hm, hJ, hJi.trans hb, hJu, huv, hP, fun a => (hcoeff a).trans hb,
    fun l hl => ⟨(hbound l hl).1.trans hb, (hbound l hl).2⟩,
    fun z => (hA z).mono hb hB, fun z => (hC z).mono hb hB, hfit, hfloor⟩

/-- A natural-number complexity budget can dominate both the old degree and
any prescribed positive rescaling of its exponent. -/
theorem exists_scaled_budget (B : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ B' : ℕ, B ≤ B' ∧ (B : ℝ) ≤ α * (B' : ℝ) := by
  let B' : ℕ := max B ⌈(B : ℝ) / α⌉₊
  refine ⟨B', le_max_left _ _, ?_⟩
  have hceil : (B : ℝ) / α ≤ (B' : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right B ⌈(B : ℝ) / α⌉₊))
  have := (div_le_iff₀ hα).mp hceil
  nlinarith


/-- Transport charts back from the power-scaled resolution. -/
theorem chartData_unscale {p : Problem} {α : ℝ} (hα : α ≠ 0) (M : ℕ)
    {B B' k T n : ℕ} {r b h ε : ℝ} {truth : Bool}
    {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hN : 1 ≤ p.N k) (hB : B ≤ B') (hBe : α * (B : ℝ) ≤ (B' : ℝ))
    (hc : ChartData (powerScale p α M) B r b h ε truth k T n γ j A C u v J P Λ) :
    ChartData p B' (α * r) (α * b) (α * h) (α * ε) truth k
      T n γ j A C u v J P Λ := by
  have hp (z : ℝ) : (p.N k ^ α) ^ z = p.N k ^ (α * z) := scaled_power (by linarith)
  have hb : p.N k ^ (α * (B : ℝ)) ≤ p.N k ^ (B' : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN hBe
  simp only [ChartData, powerScale_N, powerScale_E, powerScale_w, powerScale_f,
    mu_powerScale, hp, mul_neg, mul_div_cancel₀ _ hα] at hc
  rcases hc with ⟨ht, hn, hmeas, hdisj, hsub, hc, hlist, hlmeas, hcover, hmass⟩
  refine ⟨ht, hn.trans hb, hmeas, hdisj, hsub, ?_, hlist, hlmeas, hcover, hmass⟩
  intro i
  rcases hc i with ⟨hm, hJ, hJi, hJu, huv, hP, hcoeff, hbound, hA, hC, hfit, hfloor⟩
  exact ⟨hm, hJ, hJi.trans hb, hJu, huv, hP, fun a => (hcoeff a).trans hb,
    fun l hl => ⟨(hbound l hl).1.trans hb, (hbound l hl).2⟩,
    fun z => (hA z).mono hb hB, fun z => (hC z).mono hb hB, hfit, hfloor⟩

/-- The chart cost is divided by exactly the same factor as depth. -/
theorem cost_powerScale_iff {p : Problem} (hN : ∀ k, 1 ≤ p.N k)
    {α : ℝ} (hα : 0 < α) (M : ℕ) (h : ℝ) :
    Cost (powerScale p α M) h ↔ Cost p (α * h) := by
  constructor
  · rintro ⟨hh, B, hB, hc⟩
    let B' : ℕ := max B ⌈α * (B : ℝ)⌉₊
    have hBB' : B ≤ B' := le_max_left _ _
    have hexp : α * (B : ℝ) ≤ (B' : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right B ⌈α * (B : ℝ)⌉₊))
    refine ⟨mul_nonneg hα.le hh, B', hB.trans hBB', ?_⟩
    intro ε hε
    apply (hc (ε / α) (div_pos hε hα)).mono
    intro k hk
    rcases hk with ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hc⟩
    refine ⟨T, n, γ, j, A, C, u, v, J, P, Λ, ?_⟩
    have H := chartData_unscale hα.ne' M (hN k) hBB' hexp hc
    simpa only [powerScale_L, mul_add, mul_div_cancel₀ _ hα.ne'] using H
  · rintro ⟨hh, B, hB, hc⟩
    obtain ⟨B', hBB', hexp⟩ := exists_scaled_budget B hα
    refine ⟨(mul_nonneg_iff_of_pos_left hα).mp hh, B', hB.trans hBB', ?_⟩
    intro ε hε
    apply (hc (α * ε) (mul_pos hα hε)).mono
    intro k hk
    rcases hk with ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hc⟩
    refine ⟨T, n, γ, j, A, C, u, v, J, P, Λ, ?_⟩
    apply chartData_powerScale hα.ne' M (hN k) hBB' hexp
    simpa only [powerScale_L, mul_add, mul_div_cancel₀ _ hα.ne'] using hc

/-- The horizon inherits the exact scaling of all chart costs. -/
theorem horizon_powerScale {p : Problem} (hN : ∀ k, 1 ≤ p.N k)
    (hne : ∃ h, Cost p h) {α : ℝ} (hα : 0 < α) (M : ℕ) :
    Horizon (powerScale p α M) = Horizon p / α := by
  have hbdd : BddBelow {h | Cost p h} := ⟨0, fun _ hh => hh.1⟩
  have himage : {h | Cost (powerScale p α M) h} =
      (fun h : ℝ => h * α⁻¹) '' {h | Cost p h} := by
    ext h
    rw [Set.mem_ofPred_eq, cost_powerScale_iff hN hα M]
    constructor
    · intro hh
      exact ⟨α * h, hh, by field_simp⟩
    · rintro ⟨g, hg, rfl⟩
      simpa only [Set.mem_ofPred_eq, mul_left_comm α, mul_inv_cancel₀ hα.ne', one_mul, mul_one] using hg
  unfold Horizon
  rw [himage, div_eq_mul_inv]
  exact ((isGLB_csInf hne hbdd).mul_right (inv_nonneg.mpr hα.le)).csInf_eq
    (Set.Nonempty.image _ hne)

/-- Length rescaling, with the exact relative profile and horizon identities. -/
theorem length_rescaling {p : Problem} (hp : Exact p) {α : ℝ} (hα : 0 < α)
    (hne : ∃ h, Cost p h) :
    ∃ q : Problem, Exact q ∧ q.L = p.L / α ∧ q.d = p.d ∧ q.S = p.S ∧
      q.U = p.U / α ∧ Horizon q = Horizon p / α ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ q.L →
        q.f r - q.f 0 = (p.f (α * r) - p.f 0) / α := by
  have hN : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1.1 k]
  have hNt := (tendsto_rpow_atTop hα).comp hp.1.2.1
  obtain ⟨m, hm⟩ := eventually_atTop.mp (hNt.eventually (eventually_ge_atTop 2))
  obtain ⟨M, hMM, hexp⟩ := exists_scaled_budget p.M hα
  let p' := reindex p (fun k => k + m)
  have hp' : Exact p' := exact_reindex hp _ (tendsto_add_atTop_nat m)
  have hscale : ∀ k, 2 ≤ p'.N k ^ α := fun k => hm (k + m) (by omega)
  let q := powerScale p' α M
  refine ⟨q, exact_powerScale hp' hα (hp.1.2.2.2.1.trans hMM) hexp hscale,
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [horizon_powerScale (fun k => hN (k + m))
      (by
        obtain ⟨h, hh⟩ := hne
        exact ⟨h, (cost_shift_iff p m h).mpr hh⟩) hα M, horizon_shift]
  · intro r hr hrL
    change p.f (α * r) / α - p.f (α * 0) / α = _
    simp only [mul_zero, sub_div]

end Submission.Obl.k4_scalar_chart_normalization
