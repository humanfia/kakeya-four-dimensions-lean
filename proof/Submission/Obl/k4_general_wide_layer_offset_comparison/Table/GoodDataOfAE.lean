import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.GoodData
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SourceSheetFamilies

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

def LayerOffsetsAt (k : ℕ) (r u v m Hf : ℝ) (L : Fin 3 → ProjectedLayer α)
    (ω : α × ℝ) : Prop :=
  ∀ (c : Fin 2) (Q : Fin (p.n k r)) (i : Fin (L 0).count) (j : Fin (L c.succ).count),
    ω.1 ∈ p.B k r Q → ω.2 ∈ block (p.T k r) (p.j k r Q) →
    ω.1 ∈ (L 0).C i → ω.1 ∈ (L c.succ).C j →
    ∀ z ∈ p.trueFiberBox k r m Hf Q ((L 0).tag i),
      |eval ![z 0, z 2] ((L c.succ).G j) - eval ![z 0, z 2] ((L 0).G i) -
        p.canonicalOffset k r m (L 0) (L c.succ) Q i j| ≤ p.N k ^ (-r - ![u, v] c)

def StoredWitnessAt (k : ℕ) (r u v m δ : ℝ) (L : Fin 3 → ProjectedLayer α)
    (wit : Measure (α × ℝ)) (ω : α × ℝ) : Prop :=
  ∀ (a : Fin 3) (i : Fin (L a).count), ω.1 ∈ (L a).C i →
    ENNReal.ofReal (δ * (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
      (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
      (p.N k ^ (-(![r, r + u, r + v] a))) ^ p.d)) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (L a).tag i 0} ≤
      wit (p.witnessSet k r (L a) i (p.shortDomainCode k r ω))

def NativeChoicesAt (k : ℕ) (r m : ℝ) (L : ProjectedLayer α)
    (fwd : Fin (p.n k r) → (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) → Finset (Fin L.count))
    (rev : Fin L.count → (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) → Finset (Fin (p.n k r)))
    (ω : α × ℝ) : Prop :=
  ∀ (Q : Fin (p.n k r)) (i : Fin L.count),
    ω.1 ∈ p.B k r Q → ω.2 ∈ block (p.T k r) (p.j k r Q) → ω.1 ∈ L.C i →
      i ∈ fwd Q (p.shortComparisonCode k r m ω) ∧
      Q ∈ rev i (p.shortComparisonCode k r m ω)

/-- The actual almost-everywhere statements are placed on one measurable
full-mass carrier. No extra deletion or new assignment enters the table. -/
theorem exists_goodTableData_of_ae (hp : p.Valid)
    {k : ℕ} {r u v m H₀ Hf R : ℝ} (hat : p.AtDepth k r R)
    (hχw : p.N k ^ (-m) ≤ (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
    (hχg : p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r))
    (L : Fin 3 → ProjectedLayer α)
    (hL : ∀ a, (L a).Valid p k (![r, r + u, r + v] a) m H₀)
    (hcoeff : ∀ a i e, |((L a).G i).coeff e| ≤ p.N k ^ (m / 1000))
    (law : Measure (α × ℝ)) (hle : law ≤ p.ρ k)
    (hcover : ∀ a, (L a).Covers law)
    (hpalette : ∀ᵐ ω ∂law,
      0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋})
    (hoffsets : ∀ᵐ ω ∂law, p.LayerOffsetsAt k r u v m Hf L ω)
    (wit : Measure (α × ℝ)) (hwit : wit ≤ p.μ k) {δ : ℝ} (hδ : 0 < δ)
    (hwitness : ∀ᵐ ω ∂law, p.StoredWitnessAt k r u v m δ L wit ω)
    (Knat : ℝ)
    (fwd : Fin (p.n k r) → (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) → Finset (Fin (L 0).count))
    (rev : Fin (L 0).count → (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) → Finset (Fin (p.n k r)))
    (hfwd : ∀ Q c, ((fwd Q c).card : ℝ) ≤ Knat)
    (hrev : ∀ i c, ((rev i c).card : ℝ) ≤ Knat)
    (hnative : ∀ᵐ ω ∂law, p.NativeChoicesAt k r m (L 0) fwd rev ω)
    (smax : ℝ) (hsmax : ∀ c : Fin 2, r + ![u, v] c ≤ smax)
    (hband : ∀ ω ∈ p.baseGood k, ∀ (G : MvPolynomial (Fin 2) ℝ) (x Δ : ℝ), G.totalDegree ≤ 2 →
      (∀ e, |G.coeff e| ≤ p.N k ^ (m / 1000)) → p.N k ^ (-smax) ≤ Δ →
      wit (p.comparisonBand k m ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
        ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
        (![⌊p.b k ω.1 3 / p.N k ^ (-m)⌋, ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋])
        (p.shortDomainCode k r ω) (G + MvPolynomial.C x) Δ) ≤
      ENNReal.ofReal (16800 * p.K k ^ 2 * p.N k ^ (-m) * (2 : ℝ) ^ (-(p.T k r : ℤ)) *
        ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) * Δ ^ p.d) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋}) :
    ∃ t : p.GoodTableData k r u v m H₀ Hf,
      t.law = law ∧ t.layers = L ∧ t.wit = wit ∧ t.δ = δ ∧ t.Knat = Knat := by
  have hμ : law ≤ p.μ k := hle.trans (hp.basic k).2.2.2.2.1
  have hb := (Basic.ae_baseGood p hp.basic k).filter_mono (ae_mono hμ)
  have ht := (Basic.ae_short_time_code p hp.basic k r m).filter_mono (ae_mono hμ)
  have htrue := hat.2.2.2.2.2.1.filter_mono (ae_mono hμ)
  have hlabels : ∀ᵐ ω ∂law, ∀ a : Fin 3, ∃ i, ω.1 ∈ (L a).C i := ae_all_iff.mpr hcover
  let P : α × ℝ → Prop := fun ω =>
    ω ∈ p.baseGood k ∧
    (∃ Q, ω.1 ∈ p.B k r Q ∧ ω.2 ∈ block (p.T k r) (p.j k r Q)) ∧
    (∀ Q : Fin (p.n k r), ω.2 ∈ block (p.T k r) (p.j k r Q) →
      ⌊ω.2 / (2 : ℝ) ^ (-(p.T k r : ℤ))⌋ = ((p.j k r Q : ℕ) : ℤ)) ∧
    (∀ a : Fin 3, ∃ i, ω.1 ∈ (L a).C i) ∧
    (0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋}) ∧
    p.LayerOffsetsAt k r u v m Hf L ω ∧ p.StoredWitnessAt k r u v m δ L wit ω ∧
    p.NativeChoicesAt k r m (L 0) fwd rev ω
  have hP : ∀ᵐ ω ∂law, P ω := by
    filter_upwards [hb, htrue, ht, hlabels, hpalette, hoffsets, hwitness, hnative]
      with ω hbω hQω htω hLω hpω hoω hwω hnω
    exact ⟨hbω, hQω, htω, hLω, hpω, hoω, hwω, hnω⟩
  obtain ⟨G, hG, hnull, hgood⟩ :=
    Native.SheetComparison.measurable_full_source law P hP
  exact ⟨{
    basic := hp.basic
    N_one := by linarith [hp.scale k]
    K_one := hp.subpower.1 k
    chi_width := hχw
    chi_slope := hχg
    R := R
    atDepth := hat
    layers := L
    layer_valid := hL
    coefficient_bound := hcoeff
    law := law
    le_rho := hle
    good := G
    good_measurable := hG
    law_good := hnull
    good_base := fun ω hω => (hgood ω hω).1
    good_true := fun ω hω => (hgood ω hω).2.1
    good_time := fun ω hω => (hgood ω hω).2.2.1
    good_label := fun ω hω => (hgood ω hω).2.2.2.1
    good_palette := fun ω hω => (hgood ω hω).2.2.2.2.1
    good_offset := fun ω hω => (hgood ω hω).2.2.2.2.2.1
    wit := wit
    wit_le := hwit
    δ := δ
    δ_pos := hδ
    good_witness := fun ω hω => (hgood ω hω).2.2.2.2.2.2.1
    Knat := Knat
    fwd := fwd
    rev := rev
    fwd_card := hfwd
    rev_card := hrev
    good_native := fun ω hω => (hgood ω hω).2.2.2.2.2.2.2
    smax := smax
    smax_fine := hsmax
    band_cap := fun ω hω => hband ω ((hgood ω hω).1) }, rfl, rfl, rfl, rfl, rfl⟩

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
