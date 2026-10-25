import Submission.Obl.k4_known_atlas_normalization_composition.Definitions

namespace Submission.Obl.k4_known_atlas_normalization_composition

open MeasureTheory Filter

/-- A narrow terminal atlas at one sample. -/
def NarrowTerminalAt (p : Data) (M D : ℕ) (h w ε : ℝ) (k : ℕ) : Prop :=
  ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
    (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧
    (∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-w + ε)) ∧
    a.TrueAt M D p.L

def NarrowTerminal (p : Data) (h w : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, NarrowTerminalAt p M D h w ε k

/-- An atlas with original terminal-observation lists and inverse-subpower mass.
The parent atlas carries no true-floor assumption. -/
def KnownAt (p : Data) (M D : ℕ) (r h w ε : ℝ) (k : ℕ) : Prop :=
  ∃ (a : Atlas p k) (lst : Fin (p.W k) → Observation → Finset (Fin a.C)),
    1 ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
    (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧
    (∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-w + ε)) ∧
    (a.C : ℝ) ≤ p.N k ^ M ∧ a.Separated ∧
    (∀ γ o, ((lst γ o).card : ℝ) ≤ a.κ) ∧
    (∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r (p.B k (a.γ b))
      (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b)
      (∀ z ∈ a.F b, b ∈ lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))) ∧
    ENNReal.ofReal a.κ⁻¹ ≤ a.mass

def Known (p : Data) (r h w : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, KnownAt p M D r h w ε k

/-- The required normalization theorem written with complete numerical data. -/
def Composition : Prop :=
  ∀ (p : Data), p.Valid → ∀ r h w : ℝ, 0 ≤ r → r < p.L → Known p r h w →
    ∃ q : Data, q.Valid ∧ q.L = p.L - r ∧ q.d = p.d ∧ q.S = p.S ∧ q.η = p.η ∧
      (∀ h' e : ℝ, 0 < e → Terminal q h' → Terminal p (h + h' + e)) ∧
      (∀ h' w' : ℝ, NarrowTerminal q h' w' → NarrowTerminal p (h + h') (w + w'))

/-- A finite lift certificate. Its format is fixed before sample tolerances.
Each individual child atlas can be lifted, retaining its true floor. -/
def SampleTransfer (p q : Data) (φ : ℕ → ℕ) (h w : ℝ) : Prop :=
  ∀ M D : ℕ, ∃ M' D' : ℕ, ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
    ∀ᶠ k in atTop,
      (∀ h' : ℝ, TerminalAt q M D h' ε' k →
        TerminalAt p M' D' (h + h' + ε) ε (φ k)) ∧
      (∀ h' w' : ℝ, NarrowTerminalAt q M D h' w' ε' k →
        NarrowTerminalAt p M' D' (h + h') (w + w') ε (φ k))

/-- Frequent samples in a subsequence give frequent samples of the original
sequence, provided the indexing map tends to infinity. -/
theorem frequently_of_subsequence {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {P : ℕ → Prop} (hP : ∃ᶠ k in atTop, P (φ k)) : ∃ᶠ k in atTop, P k := by
  by_contra h
  exact hP (hφ.eventually (not_frequently.mp h))

/-- All asymptotic quantifiers follow from a finite lift with fixed format. -/
theorem SampleTransfer.terminal {p q : Data} {φ : ℕ → ℕ} {h w : ℝ}
    (hlift : SampleTransfer p q φ h w) (hφ : Tendsto φ atTop atTop)
    (hN : ∀ k, 1 ≤ p.N k) {h' e : ℝ} (he : 0 < e) (ht : Terminal q h') :
    Terminal p (h + h' + e) := by
  obtain ⟨M, D, ht⟩ := ht
  obtain ⟨M', D', hlift⟩ := hlift M D
  refine ⟨M', D', fun ε hε => ?_⟩
  obtain ⟨ε', hε', hsample⟩ := hlift (min ε e) (lt_min hε he)
  apply frequently_of_subsequence hφ
  apply ((ht ε' hε').and_eventually hsample).mono
  rintro k ⟨hk, hl⟩
  obtain ⟨a, hκ, hK, hεa, hT, htrue⟩ := (hl.1 h' hk)
  refine ⟨a, hκ, hK, hεa.trans ?_, hT.trans ?_, htrue⟩
  · exact Real.rpow_le_rpow_of_exponent_le (hN _) (min_le_left _ _)
  · apply Real.rpow_le_rpow_of_exponent_le (hN _)
    linarith [min_le_right ε e]

theorem SampleTransfer.narrow {p q : Data} {φ : ℕ → ℕ} {h w : ℝ}
    (hlift : SampleTransfer p q φ h w) (hφ : Tendsto φ atTop atTop)
    {h' w' : ℝ} (ht : NarrowTerminal q h' w') :
    NarrowTerminal p (h + h') (w + w') := by
  obtain ⟨M, D, ht⟩ := ht
  obtain ⟨M', D', hlift⟩ := hlift M D
  refine ⟨M', D', fun ε hε => ?_⟩
  obtain ⟨ε', hε', hsample⟩ := hlift ε hε
  apply frequently_of_subsequence hφ
  exact ((ht ε' hε').and_eventually hsample).mono fun k hk => hk.2.2 h' w' hk.1

/-- A calibrated homogeneous remainder and its finite lifting certificate give
both conclusions simultaneously, with the original cap parameters. -/
theorem composition_of_sampleTransfer
    (hremainder : ∀ (p : Data), p.Valid → ∀ r h w : ℝ,
      0 ≤ r → r < p.L → Known p r h w →
      ∃ (q : Data) (φ : ℕ → ℕ), q.Valid ∧ q.L = p.L - r ∧ q.d = p.d ∧
        q.S = p.S ∧ q.η = p.η ∧ Tendsto φ atTop atTop ∧ SampleTransfer p q φ h w) :
    Composition := by
  intro p hp r h w hr hrL hk
  obtain ⟨q, φ, hq, hL, hd, hS, hη, hφ, hlift⟩ := hremainder p hp r h w hr hrL hk
  exact ⟨q, hq, hL, hd, hS, hη,
    fun _ _ he ht => hlift.terminal hφ (fun k => (hp.1 k).trans' (by norm_num)) he ht,
    fun _ _ ht => hlift.narrow hφ ht⟩

end Submission.Obl.k4_known_atlas_normalization_composition
