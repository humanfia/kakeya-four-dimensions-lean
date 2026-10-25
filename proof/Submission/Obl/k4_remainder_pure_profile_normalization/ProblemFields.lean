import Submission.Obl.k4_remainder_pure_profile_normalization.Definitions
namespace Submission.Obl.k4_remainder_pure_profile_normalization

theorem Data.Valid.N_ge {p : Data} (hp : p.Valid) (k : ℕ) : 2 ≤ p.N k := hp.1 k

theorem Data.Valid.L_pos {p : Data} (hp : p.Valid) : 0 < p.L := hp.2.2.2.1

end Submission.Obl.k4_remainder_pure_profile_normalization
