/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/TwoSided.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/TwoSided.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Kappa
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Bridge

/-! Two-sided horizons and known atlases: the input and output forms of terminal
extension (paper Lemma 3.5), stated for the packaged `Data`.

Terminal extension needs a true terminal system whose time exponent is within `ε` of
`h` on both sides, while `Terminal p h` only bounds `2^T ≤ N^h`; time refinement is not
free (`∑ |Q| ≤ κ / 2^T`).  `exists_twoSided_of_terminal` extracts, by compactness of
the attained time exponents, a two-sided horizon `h* ≤ h` with `Terminal p h'` for every
`h' > h*`; in particular `horizon p ≤ h*`. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Filter Topology Set

/-- A true terminal system with time exponent within `ε` of `h` on both sides.  As in
the input of terminal extension, `K k ≤ κ` is not required. -/
def TwoSidedAt (p : Data) (M D : ℕ) (h ε : ℝ) (k : ℕ) : Prop :=
  ∃ a : Atlas p k, 1 ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
    p.N k ^ (h - ε) ≤ (2 : ℝ) ^ a.T ∧ (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧ a.TrueAt M D p.L

/-- Fixed format, then for every tolerance arbitrarily late two-sided systems. -/
def TwoSided (p : Data) (h : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, TwoSidedAt p M D h ε k

/-- One sample of a known atlas at depth `r`, horizon `h`: chart conditions at depth `r`,
labels known through lists of size at most `κ` by the terminal observation `p_L`. -/
def KnownAt (p : Data) (M D : ℕ) (r h ε : ℝ) (k : ℕ) : Prop :=
  ∃ (a : Atlas p k) (lst : Fin (p.W k) → Observation → Finset (Fin a.C)),
    1 ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧ (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧
    (a.C : ℝ) ≤ p.N k ^ M ∧ a.Separated ∧ (∀ γ₁ o, ((lst γ₁ o).card : ℝ) ≤ a.κ) ∧
    (∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r (p.B k (a.γ b)) (p.E k (a.γ b))
      (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b)
      (∀ q ∈ a.F b, b ∈ lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) q))) ∧
    ENNReal.ofReal a.κ⁻¹ ≤ a.mass

/-- A known atlas at depth `r` with horizon `h`, in fixed format. -/
def KnownAtlas (p : Data) (r h : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, KnownAt p M D r h ε k

/-- Terminal extension (Lemma 3.5) for packaged data. -/
def TerminalExtensionData : Prop :=
  ∀ (d₀ S η : ℝ), d₀ < 1 → 0 < S → 0 < η → ∃ Cx cx : ℝ, 0 < Cx ∧ 0 < cx ∧
    ∀ p : Data, p.Valid → p.S = S → p.η = η → p.d ≤ d₀ →
    ∀ h e : ℝ, 0 < e → e < h → e < cx * p.L → TwoSided p h →
    ∃ L₁ : ℝ, 0 < L₁ ∧ L₁ < p.L ∧ p.L - L₁ ≤ Cx * e ∧ KnownAtlas p L₁ (h - e)

theorem terminalExtensionData_of (hTE : TerminalExtension) : TerminalExtensionData := by
  intro d₀ S η hd₀ hS hη
  obtain ⟨Cx, cx, hCx, hcx, hte⟩ := hTE d₀ S η hd₀ hS hη
  refine ⟨Cx, cx, hCx, hcx, ?_⟩
  rintro ⟨N, K, L, d, S', η', W, ω, ν, E, P, B, f, g, G⟩ hp rfl rfl hd h e he heh hecx
    ⟨M, D, hs⟩
  obtain ⟨L₁, hL₁, hL₁L, hLL₁, M', D', ho⟩ := hte N K L d W ω ν E P B f g G hp hd h e he heh
    hecx ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk => by
      obtain ⟨a, h1, hε', hlo, hhi, hC, hsep, hch, hmass⟩ := hk
      exact ⟨a.κ, h1, hε', a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F, hlo, hhi, hC,
        hsep, hch, hmass⟩⟩
  refine ⟨L₁, hL₁, hL₁L, hLL₁, M', D', fun ε hε => (ho ε hε).mono fun k hk => ?_⟩
  obtain ⟨κ, h1, hε', T, C, γ, j, c, u, Q, R, A, F, lst, hT, hC, hsep, hlst, hch, hmass⟩ := hk
  exact ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩, lst, h1, hε', by simpa [sub_add_eq_add_sub] using hT,
    hC, hsep, hlst, hch, hmass⟩

/-! ### The time exponent of a dyadic time length -/

theorem log_pos_of_two_le {N : ℝ} (hN : 2 ≤ N) : 0 < Real.log N :=
  Real.log_pos (by linarith)

/-- `2^T = N^x` with `x = T log 2 / log N`. -/
theorem two_pow_eq_rpow {N : ℝ} (hN : 2 ≤ N) (T : ℕ) :
    (2 : ℝ) ^ T = N ^ ((T : ℝ) * Real.log 2 / Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hlog := log_pos_of_two_le hN
  rw [Real.rpow_def_of_pos hN0]
  have : Real.log N * ((T : ℝ) * Real.log 2 / Real.log N) = (T : ℝ) * Real.log 2 := by
    field_simp
  rw [this, ← Real.log_pow, Real.exp_log (by positivity)]

theorem rpow_le_rpow_iff_of_two_le {N a b : ℝ} (hN : 2 ≤ N) : N ^ a ≤ N ^ b ↔ a ≤ b :=
  Real.rpow_le_rpow_left_iff (by linarith)

/-- Extraction of a two-sided horizon by compactness of the attained time exponents. -/
theorem exists_twoSided_of_terminal {p : Data} (hp : p.Valid) {h₀ : ℝ}
    (hT : Terminal p h₀) :
    ∃ h : ℝ, 0 ≤ h ∧ h ≤ h₀ ∧ TwoSided p h ∧ ∀ h' : ℝ, h < h' → Terminal p h' := by
  obtain ⟨M, D, hs⟩ := hT
  -- one sample for each tolerance `1/(n+1)`, along a strictly increasing sequence
  obtain ⟨φ, hφ, hφs⟩ := extraction_forall_of_frequently
    (P := fun n k => TerminalAt p M D h₀ (1 / ((n : ℝ) + 1)) k)
    (fun n => hs _ (by positivity))
  choose a ha1 haK haε haT hatrue using hφs
  set x : ℕ → ℝ := fun n => ((a n).T : ℝ) * Real.log 2 / Real.log (p.N (φ n)) with hx
  have hNge : ∀ n, 2 ≤ p.N (φ n) := fun n => hp.N_ge _
  have hpow : ∀ n, (2 : ℝ) ^ (a n).T = p.N (φ n) ^ x n := fun n => two_pow_eq_rpow (hNge n) _
  have hxmem : ∀ n, x n ∈ Icc 0 h₀ := by
    intro n
    refine ⟨by have := log_pos_of_two_le (hNge n); positivity, ?_⟩
    have h := haT n
    rw [hpow n] at h
    exact (rpow_le_rpow_iff_of_two_le (hNge n)).mp h
  obtain ⟨hs', hs'mem, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hxmem
  -- eventual properties along `ψ`
  have hcomp : Tendsto (fun n => φ (ψ n)) atTop atTop :=
    (hφ.comp hψ).tendsto_atTop
  have htol : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, 1 / ((ψ n : ℝ) + 1) ≤ ε := by
    intro ε hε
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (h1.comp hψ.tendsto_atTop).eventually (ge_mem_nhds hε)
    exact h2
  have hslack : ∀ n ε, 1 / ((ψ n : ℝ) + 1) ≤ ε →
      (a (ψ n)).κ ≤ p.N (φ (ψ n)) ^ ε := fun n ε hle =>
    (haε (ψ n)).trans (Real.rpow_le_rpow_of_exponent_le (by linarith [hNge (ψ n)]) hle)
  refine ⟨hs', hs'mem.1, hs'mem.2, ⟨M, D, fun ε hε => ?_⟩, fun h' hh' => ⟨M, D, fun ε hε => ?_⟩⟩
  · rw [frequently_atTop]
    intro K₀
    have hev : ∀ᶠ n in atTop, K₀ ≤ φ (ψ n) ∧ 1 / ((ψ n : ℝ) + 1) ≤ ε ∧
        |x (ψ n) - hs'| ≤ ε := by
      refine (hcomp.eventually (eventually_ge_atTop K₀)).and ((htol ε hε).and ?_)
      have := (hlim.sub_const hs').abs
      simp only [sub_self, abs_zero] at this
      exact this.eventually (ge_mem_nhds hε)
    obtain ⟨n, hK₀, hn1, hn2⟩ := hev.exists
    refine ⟨φ (ψ n), hK₀, a (ψ n), ha1 _, hslack n ε hn1, ?_, ?_, hatrue _⟩
    · rw [hpow, rpow_le_rpow_iff_of_two_le (hNge _)]
      have := (abs_le.mp hn2).1
      linarith
    · rw [hpow, rpow_le_rpow_iff_of_two_le (hNge _)]
      have := (abs_le.mp hn2).2
      linarith
  · rw [frequently_atTop]
    intro K₀
    have hev : ∀ᶠ n in atTop, K₀ ≤ φ (ψ n) ∧ 1 / ((ψ n : ℝ) + 1) ≤ ε ∧ x (ψ n) ≤ h' := by
      refine (hcomp.eventually (eventually_ge_atTop K₀)).and ((htol ε hε).and ?_)
      exact hlim.eventually (ge_mem_nhds hh')
    obtain ⟨n, hK₀, hn1, hn2⟩ := hev.exists
    refine ⟨φ (ψ n), hK₀, a (ψ n), ha1 _, haK _, hslack n ε hn1, ?_, hatrue _⟩
    rw [hpow, rpow_le_rpow_iff_of_two_le (hNge _)]
    exact hn2

/-- The extracted two-sided horizon bounds the horizon from above. -/
theorem horizon_le_of_forall_terminal {p : Data} (hp : p.Valid) {h : ℝ}
    (hT : ∀ h' : ℝ, h < h' → Terminal p h') : horizon p ≤ h := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro h' hh'
  exact horizon_le hp (hT h' hh')

/-- A two-sided horizon is attained above the horizon. -/
theorem horizon_le_of_twoSided {p : Data} (hp : p.Valid) {h : ℝ} (hT : TwoSided p h) :
    horizon p ≤ h := by
  apply horizon_le_of_forall_terminal hp
  intro h' hh'
  obtain ⟨M, D, hs⟩ := hT
  refine ⟨M, D, fun ε hε => ?_⟩
  set ε' := min ε (h' - h) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by linarith)
  have hK := hp.K_subpower hε
  refine ((hs ε' hε'pos).and_eventually hK).mono fun k ⟨hk, hKk⟩ => ?_
  obtain ⟨a, h1, hκ, _, hhi, htrue⟩ := hk
  have hN : 2 ≤ p.N k := hp.N_ge k
  refine TerminalAt.of_trueAt hp a h1 (hκ.trans ?_) hKk (hhi.trans ?_) htrue
  · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (min_le_left _ _)
  · refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    have := min_le_right ε (h' - h)
    linarith

end Submission.Obl.k4_balanced_native_packet_transport.CPF
