import Submission.Obl.k4_clean_cover_graph_atlas.GlobalSheetData
import Submission.Obl.k4_clean_cover_graph_atlas.SampleCaps

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets
section
variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
  {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ}
  {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
  {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
  {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}

variable {Mpr Dpr Mg Dg : ℕ} {d₁ ρ gain τ ε : ℝ} {n : ℕ} {old : Fin n → Fin C}
  {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
  {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ} {i : ℕ} {h : ℝ} {s₀ K : ℕ}

open Classical in
/-- Concrete finite sample assembly: sheets, physical roots, original component
AC and finiteness are constructed here. The remaining inputs are covered-entry
mass bookkeeping and the displayed scalar/counting budgets. -/
theorem coreOutput_of_sample_data {Csheet : ℕ} {d₀ : ℝ} {params : GroupParameters}
    (hGR : GroupRecovery.{0, 0} 2 d₀ params)
    {Rg M εg θo β : ℝ} {Mc : ℕ}
    (hR : params.radius ≤ Rg) (hM : 0 < M) (hεg : 0 < εg) (hεgp : εg ≤ params.epsilon) (hsheets : PacketSheetFamilyAt Csheet)
    (hNk : 1 ≤ Nk)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcov : ∀ e, ∀ p ∈ cov e, p ∈ V e.1 ∧
      p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧ p.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1)

    (hcovm : ∀ e, MeasurableSet (cov e))
    (hcovdisj : ∀ e e', e ≠ e' → γ (old e.1) = γ (old e'.1) → Disjoint (cov e) (cov e'))
    {Abound : ℝ} (hAbound : 2 ≤ Abound)
    (hUA : 4 * Nk ^ (4 * ρ * gain * L + 4 * ε) ≤ Abound)
    (hκ4A : 4 * κ ≤ Abound) (hκA : κ + 1 ≤ Abound)
    (hδfine1 : δ Nk (r i + h * L) ≤ 1) (hδold1 : δ Nk (r i) ≤ 1)
    (hdiscFine : ∀ e, (cov e).Nonempty → ∀ d,
      |(packetDiscriminant (T i) (j (old e.1)) (c (old e.1)) (u (old e.1)) (Q (old e.1))
        (B (γ (old e.1))) (R' e.1)).coeff d| ≤ Abound)
    (hdiscOld : ∀ G : Group C s₀ K, (∃ e, (cov e).Nonempty ∧ entryGroup old e = G) → ∀ d,
      |(packetDiscriminant (T i) (j G.1) (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1)).coeff d| ≤ Abound)
    (hside : side s₀ * (κ + 2) ≤ (Abound ^ (-(Csheet : ℝ)) / 128) / 2) :
    let ob := fun G : Group C s₀ K => groupBase (T i) (j G.1) (c G.1) (u G.1) (Q G.1)
      (subBoxCenter s₀ G.2.1 (boxOf K G.2.2.1)) (Abound ^ (-(Csheet : ℝ)) / 128)
    let ηfine := Nk ^ (4 * ρ * gain * L + 4 * ε) * δ Nk (r i + h * L) * Abound ^ ((Csheet : ℝ) + 1)
    let ηold := κ * δ Nk (r i) * Abound ^ ((Csheet : ℝ) + 1)
    ∀ (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (H m : Group C s₀ K → ℝ) (hH : ∀ G, 0 < H G)
    (hcount : ∀ G, ((Finset.univ.filter (fun e : Entry n s₀ K => entryGroup old e = G)).card : ℝ) ≤
      Rg ^ (d₀ + εg))
    (hcap : ∀ e, (cov e).Nonempty →
      (ENNReal.ofReal (ω (γ (old e.1))) • ((ν (γ (old e.1))).prod volume).restrict (cov e)).map
        (ob (entryGroup old e) ∘ obs (B (γ (old e.1))) (δ Nk L)) ≤
        ENNReal.ofReal (H (entryGroup old e)) • volume)
    (hfloor : ∀ e, (cov e).Nonempty → ENNReal.ofReal (m (entryGroup old e)) ≤
      ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e))
    (hθmass : ∀ G, ENNReal.ofReal θ * volume (Metric.closedBall (0 : Real3) (1 / 2)) ≤
      ENNReal.ofReal (m G / H G))
    (hremez : params.remezScale *
      (params.remezExponent * θ ^ (-params.remezExponent) * (ηfine + ηold)) ≤ M * Rg ^ εg)
    (hwidth : 2 * ηfine + δ Nk L ≤ M * Rg ^ (-1 + εg))
    -- bounds of the tests and scales, and the output threshold
    (hsourceBudget : 8 * Nk ^ Mg ≤ Nk ^ Mc)
    (hscaleBudget : ∀ w, B w * Abound + 4 * Nk ^ Mg ≤ Nk ^ Mc)
    (hinverseBudget : ∀ w,
      (1 + 80 * ((ηfine + (∑ i, groupJetWidth params Rg M εg i) / params.lower) / B w)) *
        (Abound / B w + Abound ^ (20 : ℕ) / B w ^ 2) ≤ Nk ^ Mc)
    (hthr : 340 * (ηfine + (∑ i, groupJetWidth params Rg M εg i) / params.lower) ≤
      δ Nk (r i) * Nk ^ (-(θo * h * L)))
    -- group observation domains, list sizes and the total
    (S : Group C s₀ K → Set (EuclideanSpace ℝ (Fin 3) × ℤ)) (hSm : ∀ G, MeasurableSet (S G))
    (hsupp : ∀ e, ∀ p ∈ cov e, obs (B (γ (old e.1))) (δ Nk L) p ∈ S (entryGroup old e))
    (Dcount : ℕ)
    (hD : ∀ w o, ((Finset.univ.filter (fun G : Group C s₀ K => γ G.1 = w ∧ o ∈ S G)).card) ≤
      Dcount)
    (hcardE : (Fintype.card (Entry n s₀ K) : ℝ) ≤ Nk ^ Mc)
    (hlistβ : ((7 ^ Fintype.card (GroupJetIndex params) * Dcount : ℕ) : ℝ) ≤ Nk ^ β)
    (htotal : ENNReal.ofReal (Nk ^ (-β)) +
        (ENNReal.ofReal (Rg ^ (-εg)) * ∑ e, ENNReal.ofReal (ω (γ (old e.1))) *
            ((ν (γ (old e.1))).prod volume) (cov e) +
          ENNReal.ofReal (Rg ^ (-(2 * εg))) *
            ∑ e, (if (cov e).Nonempty then ENNReal.ofReal (H (entryGroup old e)) else 0)) ≤
      ∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e)),
    CoreOutput Nk L W ω ν E B (r i) h θo β Mc γ j c u Q R old R' A' (T i) s₀ K := by
  dsimp only
  intro θ hθ hθ1 H mG hH hcount hcap hfloor hθmass hremez hwidth
    hsourceBudget hscaleBudget hinverseBudget hthr S hSm hsupp Dcount hD hcardE hlistβ htotal
  let ob := fun G : Group C s₀ K => groupBase (T i) (j G.1) (c G.1) (u G.1) (Q G.1)
    (subBoxCenter s₀ G.2.1 (boxOf K G.2.2.1)) (Abound ^ (-(Csheet : ℝ)) / 128)
  let lb := fun G l t => ob G (obs (B (γ G.1)) (δ Nk L) (l, t))
  let ηfine := Nk ^ (4 * ρ * gain * L + 4 * ε) * δ Nk (r i + h * L) * Abound ^ ((Csheet : ℝ) + 1)
  let ηold := κ * δ Nk (r i) * Abound ^ ((Csheet : ℝ) + 1)
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  have hB : ∀ w, 0 < B w := fun w => (hsi.1.2.2.2 w).2.1
  have hApos : 0 < Abound := by linarith
  have hκpos : 0 < κ := zero_lt_one.trans_le hpath.1
  have hηfine : 0 < ηfine := by
    dsimp only [ηfine]
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hNkpos _) (gδ_pos Nk _))
      (Real.rpow_pos_of_pos hApos _)
  have hηold : 0 < ηold := by
    dsimp only [ηold]
    exact mul_pos (mul_pos hκpos (gδ_pos Nk _)) (Real.rpow_pos_of_pos hApos _)
  obtain ⟨Fe, F0, Pe, se, pe, hfields⟩ := exists_sample_entry_sheets hsheets hNkpos hsi hpath cov hcov
    hAbound hUA hκ4A hκA hδfine1 hδold1 hdiscFine hdiscOld hside
  have hcovV : ∀ e, cov e ⊆ V e.1 := fun e p hp => (hcov e p hp).1
  have hcovE : ∀ e, cov e ⊆ {p | p ∈ E (γ (old e.1)) ∧
      p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧ p.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1} := by
    intro e p hp
    obtain ⟨hpV, hpm, hpt⟩ := hcov e p hp
    obtain ⟨_, _, _, _, _, _, _, _, _, hVsub, _⟩ := hsi.2.2.2.2.2.2.2.1 e.1
    have hpF := (hVsub hpV).1
    have hchart := (hpath.2.2.2.2.2.2.2 (old e.1)).2.2
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hFsub, _⟩ := hchart
    exact ⟨(hFsub p hpF).1, hpm, hpt⟩
  have hηbin0 : 0 ≤ (∑ k, groupJetWidth params Rg M εg k) / params.lower := by
    apply div_nonneg (Finset.sum_nonneg fun k _ => ?_) params.lower_pos.le
    exact (mul_pos (params.upper_pos _) (mul_pos hM
      (Real.rpow_pos_of_pos (by linarith [params.radius_two]) _))).le
  apply coreOutput_of_entry_sheets_of_ac hGR hR hM hεg hεgp hB hNk (gδ_pos Nk L) (gδ_pos Nk (r i))
    cov hcovE hcovm hcovdisj
    (fun e => sampleInput_cov_finite hsi e.1 (hcovV e))
    (fun e => sampleInput_cov_observation_ac hsi e.1 (hcovV e)) ob
    (fun G => measurable_groupBase _ _ _ _ _ _ _) lb (fun G p => rfl) Fe F0 Pe se pe
    hfields.degree_scale hfields.roots ηfine ηold hηfine hηold hfields.fit_times hfields.fit_points
    θ hθ hθ1 H mG hH hcount hcap hfloor hθmass hremez hwidth ?_ ?_ hthr
    S hSm hsupp Dcount hD hcardE hlistβ htotal
  · intro e hne d
    obtain ⟨hc, hd⟩ := hfields.coefficients e hne d
    have hnonneg : 0 ≤ Nk ^ Mg := by positivity
    exact ⟨hc.trans (by linarith), hd.trans (by linarith)⟩
  · intro e hne
    obtain ⟨hs, hqc, hinv⟩ := hfields.scales e hne
    refine ⟨hs.trans (hscaleBudget _), hqc.trans hsourceBudget, ?_⟩
    have hBpos : 0 < B (γ (old e.1)) := hB _
    have hfactor : 0 ≤ 1 + 80 * ((ηfine + (∑ k, groupJetWidth params Rg M εg k) / params.lower) /
        B (γ (old e.1))) := by positivity
    calc
      _ = (1 + 80 * ((ηfine + (∑ k, groupJetWidth params Rg M εg k) / params.lower) /
          B (γ (old e.1)))) * (se e)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ _ := (mul_le_mul_of_nonneg_left hinv hfactor).trans (hinverseBudget _)

end
end Submission.Obl.k4_clean_cover_graph_atlas
