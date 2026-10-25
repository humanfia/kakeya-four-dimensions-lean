import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.SampleCore
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Contract
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Intercept

/-!
# The potential at one sample

From the field certificate of one packet at one sample, with the compact
radius covering the two exponents used (the velocity rounding width
`N^-(Z+1)` and the angular pencil width `N^-b`, `b = κ(1-d)/64`), and one
comparison `Cbig H^mbig ≤ N^η₀` between the subpower and a fixed power of
`N`, the conservativity step produces the potential.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory MvPolynomial

/-- All the numerical conditions of the sample step follow from one comparison. -/
theorem sample_conditions {X Y d κ S Z B Cbig Ccurl cK A₁ A₂ : ℝ} {D n₁ n₂ mbig : ℕ}
    (hX2 : 2 ≤ X) (hY1 : 1 ≤ Y) (hd0 : 0 ≤ d) (hd1 : d < 1) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hZ : 10 ≤ Z) (hB : Z + 10 ≤ B) (hC0 : 0 ≤ Ccurl) (hcK : 0 ≤ cK) (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂)
    (hCbig : 5 + 24 + 48 + 64 + 768 * Ccurl * cK ^ 2 + 16 * cK + 32 + 3 +
      3 * ((D : ℝ) + 1) ^ 2 * A₁ + 3 * ((D : ℝ) + 1) ^ 2 * A₂ ≤ Cbig)
    (hm : n₁ + n₂ + 2 * D + 10 ≤ mbig)
    (hbig : Cbig * Y ^ mbig ≤ X ^ (min (S * (κ * (1 - d) / 64)) (κ * (1 - d) / 1000))) :
    5 * Y ^ 2 ≤ X ^ (B - κ - Z - 1) ∧ 24 * Y ^ 1 ≤ X ^ (1 : ℝ) ∧
    48 * Y ^ 2 ≤ X ^ (S * (κ * (1 - d) / 64)) ∧ 64 * Y ^ 3 ≤ X ^ (κ / 8) ∧
    (768 * Ccurl * cK ^ 2) * Y ^ (2 * D + 4) ≤ X ^ (Z - 2 * (κ * (1 - d) / 64)) ∧
    (16 * cK) * Y ^ (D + 2) ≤ X ^ (Z - κ * (1 - d) / 64) ∧
    32 * Y ^ 0 ≤ X ^ Z ∧
    3 * Y ^ 2 ≤ X ^ (κ / 4 - 2 * (κ * (1 - d) / 1000)) ∧
    (3 * ((D : ℝ) + 1) ^ 2 * A₁) * Y ^ (n₁ + 1) ≤
      X ^ (κ * (1 - d) / 8 - 4 * (κ * (1 - d) / 64) - 2 * (κ * (1 - d) / 1000)) ∧
    (3 * ((D : ℝ) + 1) ^ 2 * A₂) * Y ^ n₂ ≤ X ^ (Z - 1 - 2 * (κ * (1 - d) / 1000)) := by
  have hX1 : 1 ≤ X := by linarith
  set u := κ * (1 - d) with hudef
  have hu0 : 0 < u := by
    have : 0 < 1 - d := by linarith
    positivity
  have huκ : u ≤ κ := by
    have : κ * (1 - d) ≤ κ * 1 := mul_le_mul_of_nonneg_left (by linarith) hκ0.le
    linarith
  have hη : min (S * (u / 64)) (u / 1000) ≤ u / 1000 := min_le_right _ _
  have hηS : min (S * (u / 64)) (u / 1000) ≤ S * (u / 64) := min_le_left _ _
  have h768 : 0 ≤ 768 * Ccurl * cK ^ 2 := by positivity
  have h16 : 0 ≤ 16 * cK := by positivity
  have h3A₁ : 0 ≤ 3 * ((D : ℝ) + 1) ^ 2 * A₁ := by positivity
  have h3A₂ : 0 ≤ 3 * ((D : ℝ) + 1) ^ 2 * A₂ := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cond_of_big hX1 hY1 (by norm_num)
      (by linarith only [hCbig, h768, h16, h3A₁, h3A₂]) (by omega)
      (by linarith only [hη, hu0, huκ, hκ1, hZ, hB]) hbig
  · exact cond_of_big hX1 hY1 (by norm_num)
      (by linarith only [hCbig, h768, h16, h3A₁, h3A₂]) (by omega)
      (by linarith only [hη, hu0, huκ, hκ1]) hbig
  · exact cond_of_big hX1 hY1 (by norm_num)
      (by linarith only [hCbig, h768, h16, h3A₁, h3A₂]) (by omega) hηS hbig
  · exact cond_of_big hX1 hY1 (by norm_num)
      (by linarith only [hCbig, h768, h16, h3A₁, h3A₂]) (by omega)
      (by linarith only [hη, hu0, huκ]) hbig
  · exact cond_of_big hX1 hY1 h768 (by linarith only [hCbig, h768, h16, h3A₁, h3A₂])
      (by omega) (by linarith only [hη, hu0, huκ, hκ1, hZ]) hbig
  · exact cond_of_big hX1 hY1 h16 (by linarith only [hCbig, h768, h16, h3A₁, h3A₂])
      (by omega) (by linarith only [hη, hu0, huκ, hκ1, hZ]) hbig
  · exact cond_of_big hX1 hY1 (by norm_num)
      (by linarith only [hCbig, h768, h16, h3A₁, h3A₂]) (by omega)
      (by linarith only [hη, hu0, huκ, hκ1, hZ]) hbig
  · exact cond_of_big hX1 hY1 (by norm_num)
      (by linarith only [hCbig, h768, h16, h3A₁, h3A₂]) (by omega)
      (by linarith only [hη, hu0, huκ]) hbig
  · exact cond_of_big hX1 hY1 h3A₁ (by linarith only [hCbig, h768, h16, h3A₁, h3A₂])
      (by omega) (by linarith only [hη, hu0]) hbig
  · exact cond_of_big hX1 hY1 h3A₂ (by linarith only [hCbig, h768, h16, h3A₁, h3A₂])
      (by omega) (by linarith only [hη, hu0, huκ, hκ1, hZ]) hbig

theorem exists_sample_potential (D : ℕ) :
    ∃ Cbig : ℝ, 1 ≤ Cbig ∧ ∃ mbig : ℕ, ∀ (Nk Hk d κ S Z B R : ℝ)
      (νg : Measure (ℕ × (Fin 5 → ℝ))) (πg : Measure ℝ) (ρg : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
      (Ag : Set (ℕ × (Fin 5 → ℝ))) (Tk : ℕ) (jj : Fin (2 ^ Tk))
      (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z₀ : Fin 2 → ℝ)
      (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ),
      FieldAt Nk Hk d κ S Z B R D νg πg ρg Ag Tk jj μ z₀ 𝒯 →
      2 ≤ Nk → 1 ≤ Hk → 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < S → 10 ≤ Z → Z + 10 ≤ B →
      R⁻¹ ≤ κ * (1 - d) / 64 → Z + 1 ≤ R →
      Cbig * Hk ^ mbig ≤ Nk ^ (min (S * (κ * (1 - d) / 64)) (κ * (1 - d) / 1000)) →
      ∃ (P : MvPolynomial (Fin 2) ℝ) (c : ℕ × (Fin 5 → ℝ) → ℝ),
        PotAt Nk (Cbig * Hk ^ mbig) (κ * (1 - d) / 1000) (D + 2) Tk jj μ z₀ P c := by
  obtain ⟨Ccurl, Cpot, hCcurl, hCpot, hcore⟩ := exists_sample_core D
  -- constants
  obtain ⟨cK, hcKdef⟩ : ∃ x : ℝ, x = 2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) + 5 := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁def⟩ : ∃ x : ℝ, x = Ccurl * cK ^ 4 * ((2 : ℝ) ^ 28) ^ (6 * D + 1) *
      (4 : ℝ) ^ (2 * D) * (2 : ℝ) ^ (6 * D + 1) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂def⟩ : ∃ x : ℝ, x = Ccurl * ((2 : ℝ) ^ (D + 2) *
      ((((D + 1) ^ 2 : ℕ) : ℝ) * (2 * ((D : ℝ) + 1)))) * ((2 : ℝ) ^ 28) ^ (2 * D) *
      (4 : ℝ) ^ (2 * D) * (2 : ℝ) ^ (2 * D) := ⟨_, rfl⟩
  obtain ⟨CH, hCHdef⟩ : ∃ x : ℝ, x = Cpot ^ 2 * ((2 : ℝ) ^ (D + 2) * (((D + 1) ^ 2 : ℕ) : ℝ)) +
      3 + (2 : ℝ) ^ (D + 2) * (((D + 1) ^ 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hcK0 : 0 ≤ cK := by rw [hcKdef]; positivity
  have hA₁ : 0 ≤ A₁ := by rw [hA₁def]; positivity
  have hA₂ : 0 ≤ A₂ := by rw [hA₂def]; positivity
  have hCH : 0 ≤ CH := by rw [hCHdef]; positivity
  obtain ⟨n₁, hn₁def⟩ : ∃ n : ℕ, n = 4 * (D + 2) + 16 * (6 * D + 1) + 4 * (2 * D) := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂def⟩ : ∃ n : ℕ, n = (D + 3) + 16 * (2 * D) + 4 * (2 * D) := ⟨_, rfl⟩
  obtain ⟨Cbig, hCbigdef⟩ : ∃ x : ℝ, x = 5 + 24 + 48 + 64 + 768 * Ccurl * cK ^ 2 + 16 * cK + 32 +
      3 + 3 * ((D : ℝ) + 1) ^ 2 * A₁ + 3 * ((D : ℝ) + 1) ^ 2 * A₂ + CH := ⟨_, rfl⟩
  obtain ⟨mbig, hmbigdef⟩ : ∃ n : ℕ, n = n₁ + n₂ + 2 * D + 10 := ⟨_, rfl⟩
  have h768 : 0 ≤ 768 * Ccurl * cK ^ 2 := by positivity
  have h16 : 0 ≤ 16 * cK := by positivity
  have h3A₁ : 0 ≤ 3 * ((D : ℝ) + 1) ^ 2 * A₁ := by positivity
  have h3A₂ : 0 ≤ 3 * ((D : ℝ) + 1) ^ 2 * A₂ := by positivity
  have hCbig1 : 1 ≤ Cbig := by
    rw [hCbigdef]
    linarith only [h768, h16, h3A₁, h3A₂, hCH]
  refine ⟨Cbig, hCbig1, mbig, ?_⟩
  intro X Y d κ S Z B R νg πg ρg Ag Tk jj μ z₀ 𝒯 hF hX2 hY1 hd0 hd1 hκ0 hκ1 hS hZ hB hRb hRZ
    hbig
  -- the numerical conditions
  obtain ⟨ca, cb, cc, cd, ce, cf, cg, cF1, cF2, cF3⟩ := sample_conditions (D := D) (n₁ := n₁)
    (n₂ := n₂) hX2 hY1 hd0 hd1 hκ0 hκ1 hZ hB hCcurl.le hcK0 hA₁ hA₂
    (by rw [hCbigdef]; linarith only [hCH]) (by omega) hbig
  rw [hcKdef] at ce cf
  rw [hA₁def, hcKdef, hn₁def] at cF2
  rw [hA₂def, hn₂def] at cF3
  -- the field certificate
  unfold FieldAt at hF
  generalize hhdef : ((2 : ℝ) ^ Tk)⁻¹ = h at hF
  obtain ⟨hA, hνprob, hπprob, hbdd, hhlo, hhhi, hh0, hh1, hνAlo, hνAhi, hμρ, hμdom, hμsupp,
    hμmass, hz₀0, hz₀, hu, hcell, hpal, h𝒯, hfield, hjoint⟩ := hF
  haveI := hνprob
  haveI := hπprob
  obtain ⟨t₀, ht₀def⟩ : ∃ x : ℝ, x = ((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk := ⟨_, rfl⟩
  have hI : Set.Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk) ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk) =
      Set.Icc t₀ (t₀ + h) := by
    rw [ht₀def, ← hhdef, add_div, one_div]
  rw [hI] at hμsupp hu hfield
  have h2T : (0 : ℝ) < (2 : ℝ) ^ Tk := by positivity
  have hjlt : ((jj : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ Tk := by
    have : (jj : ℕ) + 1 ≤ 2 ^ Tk := jj.isLt
    exact_mod_cast this
  have hblock : ∀ t ∈ Set.Icc t₀ (t₀ + h), |t| ≤ 1 := by
    intro t ht
    have h1 : 0 ≤ t₀ := by rw [ht₀def]; positivity
    have h2 : t₀ + h ≤ 1 := by
      have heq : t₀ + h = (((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk := by
        rw [ht₀def, ← hhdef, add_div, one_div]
      rw [heq, div_le_one h2T]
      exact hjlt
    rw [abs_le]
    constructor <;> linarith only [ht.1, ht.2, h1, h2]
  have ht₀I : t₀ ∈ Set.Icc t₀ (t₀ + h) := ⟨le_rfl, by linarith only [hh0]⟩
  have hX0 : 0 < X := by linarith only [hX2]
  have hu1 : κ * (1 - d) ≤ 1 := by
    have : κ * (1 - d) ≤ κ * 1 := mul_le_mul_of_nonneg_left (by linarith only [hd0]) hκ0.le
    linarith only [this, hκ1]
  have hb : κ * (1 - d) / 64 ≤ R := by linarith only [hu1, hRZ, hZ]
  have hRv : R⁻¹ ≤ Z + 1 := by linarith only [hu1, hRb, hZ]
  have hpalv := (hpal (Z + 1) hRv hRZ).2
  have hangb := (hpal (κ * (1 - d) / 64) hRb hb).1
  have hw₁hi : X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8) ≤ X ^ (-1 : ℝ) := by
    have : h ^ ((1 : ℝ) / 8) ≤ 1 := Real.rpow_le_one hh0.le hh1 (by norm_num)
    have hXm : 0 < X ^ (-1 : ℝ) := Real.rpow_pos_of_pos hX0 _
    calc
      X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8) ≤ X ^ (-1 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left this hXm.le
      _ = X ^ (-1 : ℝ) := mul_one _
  obtain ⟨hJfin, hJcard⟩ := hjoint (X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8)) le_rfl hw₁hi
  have hY0 : 0 < Y := by linarith only [hY1]
  have hμpos : μ univ ≠ 0 := by
    have h1 : 0 < ENNReal.ofReal (X ^ (-d) * h / Y) := by
      apply ENNReal.ofReal_pos.mpr
      have : 0 < X ^ (-d) := Real.rpow_pos_of_pos hX0 _
      positivity
    have h2 : 0 < ENNReal.ofReal (h / Y) := ENNReal.ofReal_pos.mpr (by positivity)
    have h3 : 0 < ENNReal.ofReal (h / Y) * νg Ag :=
      ENNReal.mul_pos h2.ne' (lt_of_lt_of_le h1 hνAlo).ne'
    exact (lt_of_lt_of_le h3 hμmass).ne'
  obtain ⟨P, Kc, hPdeg, hPcoeff, hPsup, hKc, hPvar⟩ := hcore νg πg μ Ag t₀ h z₀ 𝒯 X Y d κ S Z B
    hA hbdd hh0 hh1 hhlo hhhi hblock hμdom hμsupp hμmass hμpos hu hcell hpalv hangb
    (fun i => (h𝒯 i).1) (fun i => (h𝒯 i).2) hfield hJfin hJcard hX2 hY1 hd0 hd1 hκ0 hκ1 hZ hB
    ca cb cc cd ce cf cg cF1 cF2 cF3
  -- the envelope
  have hYm : 1 ≤ Y ^ mbig := one_le_pow₀ hY1
  have hH'1 : 1 ≤ Cbig * Y ^ mbig := one_le_mul_of_one_le_of_one_le hCbig1 hYm
  have hCHle : CH ≤ Cbig := by
    rw [hCbigdef]
    linarith only [h768, h16, h3A₁, h3A₂, hCH]
  have hYD : Y ^ (D + 2) ≤ Y ^ mbig := pow_le_pow_right₀ hY1 (by omega)
  have hYD0 : 0 ≤ Y ^ (D + 2) := by positivity
  have hCHY : CH * Y ^ (D + 2) ≤ Cbig * Y ^ mbig :=
    mul_le_mul hCHle hYD hYD0 (by linarith only [hCbig1])
  obtain ⟨G, hGdef⟩ : ∃ x : ℝ, x = 2 ^ (D + 2) * (((D + 1) ^ 2 : ℕ) : ℝ) * Y ^ (D + 2) :=
    ⟨_, rfl⟩
  rw [← hGdef] at hKc
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  have hCHexp : CH * Y ^ (D + 2) = Cpot ^ 2 * G + 3 * Y ^ (D + 2) + G := by
    rw [hCHdef, hGdef]; ring
  have h3Y : 3 * Y ≤ 3 * Y ^ (D + 2) := by
    have : Y ≤ Y ^ (D + 2) := by
      calc Y = Y ^ 1 := (pow_one Y).symm
        _ ≤ Y ^ (D + 2) := pow_le_pow_right₀ hY1 (by omega)
    linarith only [this]
  have hCG : Cpot ^ 2 * Kc ≤ Cpot ^ 2 * G := mul_le_mul_of_nonneg_left hKc (by positivity)
  have hCG0 : 0 ≤ Cpot ^ 2 * G := by positivity
  have hcoeffH : ∀ b', |P.coeff b'| ≤ Cbig * Y ^ mbig := by
    intro b'
    have := hPcoeff b'
    linarith only [this, hCG, hCHexp, hCHY, hYD0, hG0]
  have hsupH : 3 * Y + Kc ≤ Cbig * Y ^ mbig := by
    linarith only [h3Y, hKc, hCHexp, hCHY, hCG0]
  -- the a.e. bounded lines
  have hline : ∀ᵐ p ∂μ, ∀ i, |p.1.2 i| ≤ Y := by
    have hbad : νg {l | ¬ ∀ i, |l.2 i| ≤ Y} = 0 := ae_iff.mp hbdd
    apply ae_iff.mpr
    have hsub : {p : (ℕ × (Fin 5 → ℝ)) × ℝ | ¬ ∀ i, |p.1.2 i| ≤ Y} ⊆
        {l | ¬ ∀ i, |l.2 i| ≤ Y} ×ˢ (univ : Set ℝ) := fun p hp => ⟨hp, mem_univ _⟩
    refine measure_mono_null hsub ?_
    have h1 := Measure.le_iff'.mp hμdom ({l | ¬ ∀ i, |l.2 i| ≤ Y} ×ˢ (univ : Set ℝ))
    rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, hbad, zero_mul, mul_zero] at h1
    exact le_antisymm h1 bot_le
  have hpath : ∀ᵐ p ∂μ, (∀ i, |p.1.2 i| ≤ Y) ∧ (∀ i, |ubase z₀ h p.1 t₀ i| ≤ Y) ∧
      ∀ t ∈ Set.Icc t₀ (t₀ + h), |(xL p.1 t - eval (ubase z₀ h p.1 t) P) -
        (xL p.1 t₀ - eval (ubase z₀ h p.1 t₀) P)| ≤ X ^ (-1 - 2 * (κ * (1 - d) / 1000)) := by
    filter_upwards [hline, hu, hfield] with p hlp hup hfp
    exact ⟨hlp, hup t₀ ht₀I, fun t ht => hPvar p.1 hup hfp t ht⟩
  exact ⟨P, potAt_of_potential hhdef.symm hI ht₀I hblock hPdeg hcoeffH hPsup hsupH hH'1 le_rfl
    (Real.rpow_nonneg hX0.le _) hpath⟩

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
