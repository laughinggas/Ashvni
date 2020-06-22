import tactic
import order.bounded_lattice

/- Shows that for a in with_top, a+a = 0 is equivalent to a=0. -/

example (a : with_top ℤ) : a + a = 0 ↔ a = 0 :=
begin
  split,
  { -- the hard way
    intro h, -- h is a proof of a+a=0
    -- split into cases
    cases (with_top.cases a) with htop hn,
    { -- a = ⊤
      rw htop at h,
      -- h is false
      cases h,
      -- no cases!
    },
    { -- a = n
      cases hn with n hn,
      rw hn at h ⊢,
      -- now h says n+n=0 and our goal is n=0
      -- but these are equalities in `with_top ℤ
      -- so we need to get them into ℤ
      -- A tactic called `norm_cast` does this
     norm_cast at h ⊢,
      -- we finally have a hypothesis n + n = 0
      -- and a goal n = 0      -- and everything is an integer
      rw add_self_eq_zero at h,
      assumption
    }
  },
  { -- the easy way
    intro ha,
    rw ha,
    simp
  }
end