/- Retained from this obligation, o255, branch x0901 at commit 0f8ba410.
   Earlier source attributions in this file are preserved. -/
import Submission.Obl.k4_general_parent_narrow_contact_transfer.Interface
import Submission.Obl.k4_general_parent_narrow_contact_transfer.Renewal.PreparedModel

namespace Submission.Obl.k4_general_parent_narrow_contact_transfer

open MeasureTheory Set Filter

namespace Model

variable {α : Type} [MeasurableSpace α]

/-- Numerical parameters for the attributed renewal construction. -/
def parameters (cfg : Model α) : Renewal.Parameters :=
  ⟨cfg.N, cfg.K, cfg.d, cfg.κ, cfg.ℓ, cfg.S, cfg.U, cfg.e₀⟩

/-- The renewal record contains the unchanged measures and true assignments. -/
def prepared (cfg : Model α) : Renewal.PreparedModel α :=
  ⟨cfg.ν, cfg.μ, cfg.ρ, cfg.π, cfg.b, cfg.P, cfg.T, cfg.n, cfg.j,
    cfg.A, cfg.B, cfg.c, cfg.F⟩

theorem parameters_valid {cfg : Model α} (h : Valid cfg) : (parameters cfg).Valid :=
  ⟨h.scale, h.scale_limit, h.subpower, h.dimension_nonneg, h.dimension_lt_one,
    h.rate_pos, h.rate_le_one, h.transverse_pos, h.palette_pos, h.palette_le_one,
    h.depth_pos, h.defect_pos⟩

theorem prepared_valid {cfg : Model α} (h : Valid cfg) :
    (prepared cfg).Valid (parameters cfg) := by
  refine ⟨h.basic, h.caps, ?_, h.nested⟩
  intro R hR
  filter_upwards [h.atlas R hR] with k hk
  intro s hs hsU
  have hi := hk s hs hsU
  simpa [Renewal.PreparedModel.AtlasAt, Renewal.PreparedModel.block,
    Renewal.PreparedModel.interval, Renewal.PreparedModel.q,
    Renewal.PreparedModel.width, Renewal.PreparedModel.narrow,
    Renewal.PreparedModel.x, Renewal.PreparedModel.fit,
    Submission.Lib.K4ContactNormalization.point,
    Submission.Obl.k4_critical_intercept_concentration.Data.x,
    Submission.Obl.k4_critical_intercept_concentration.Data.I,
    Submission.Obl.k4_critical_intercept_concentration.Data.fit,
    parameters, prepared] using hi

end Model

/-- A renewed model can be supplied directly to the frozen contact principle. -/
def modelOfRenewal {α : Type} [MeasurableSpace α]
    (p : Renewal.Parameters) (a : Renewal.PreparedModel α) : Model α :=
  ⟨p.N, p.K, p.d, p.kappa, p.ell, p.S, p.U, p.e₀,
    a.nu, a.mu, a.rho, a.pi, a.b, a.P, a.T, a.n, a.j, a.A, a.B, a.c, a.F⟩

theorem modelOfRenewal_valid {α : Type} [MeasurableSpace α]
    {p : Renewal.Parameters} {a : Renewal.PreparedModel α}
    (hp : p.Valid) (ha : a.Valid p) : Model.Valid (modelOfRenewal p a) := by
  obtain ⟨hN, hNt, hK, hd, hd1, hκ, hκ1, hℓ, hS, hS1, hU, he₀⟩ := hp
  obtain ⟨hbasic, hcaps, hatlas, hnested⟩ := ha
  refine ⟨hN, hNt, hK, hd, hd1, hκ, hκ1, hℓ, hS, hS1, hU, he₀,
    hbasic, hcaps, ?_, hnested⟩
  intro R hR
  filter_upwards [hatlas R hR] with k hk
  intro s hs hsU
  have hi := hk s hs hsU
  simpa [Model.Atlas, modelOfRenewal, Renewal.PreparedModel.AtlasAt,
    Renewal.PreparedModel.block, Renewal.PreparedModel.interval,
    Renewal.PreparedModel.q, Renewal.PreparedModel.width, Renewal.PreparedModel.narrow,
    Renewal.PreparedModel.x, Renewal.PreparedModel.fit,
    Submission.Lib.K4ContactNormalization.point,
    Submission.Obl.k4_critical_intercept_concentration.Data.x,
    Submission.Obl.k4_critical_intercept_concentration.Data.I,
    Submission.Obl.k4_critical_intercept_concentration.Data.fit] using hi

/-- The contact theorem is applied to an actual renewed model, with exactly
its original palette, current law, and full-assignment normalization. -/
theorem contact_result_of_renewal (hc : RawPrinciple 3)
    {α : Type} [MeasurableSpace α] {p : Renewal.Parameters} {a : Renewal.PreparedModel α}
    (hp : p.Valid) (ha : a.Valid p) (hcontact : a.Contact p) : a.Result p := by
  have h := (principle_iff 3).mp hc α (modelOfRenewal p a)
    (modelOfRenewal_valid hp ha) (fun _ => hcontact)
  exact h

end Submission.Obl.k4_general_parent_narrow_contact_transfer
