namespace CausalGeometry.Program

/-- Frozen campaign gates. CA16 is the Wilderber generalized restriction bridge. -/
inductive Campaign
  | ca00 | ca01 | ca02 | ca03 | ca04 | ca05 | ca06 | ca07 | ca08
  | ca09 | ca10 | ca11 | ca12 | ca13 | ca14 | ca15 | ca16
  deriving DecidableEq, Repr, Inhabited

def Campaign.rank : Campaign → Nat
  | .ca00 => 0 | .ca01 => 1 | .ca02 => 2 | .ca03 => 3 | .ca04 => 4
  | .ca05 => 5 | .ca06 => 6 | .ca07 => 7 | .ca08 => 8 | .ca09 => 9
  | .ca10 => 10 | .ca11 => 11 | .ca12 => 12 | .ca13 => 13
  | .ca14 => 14 | .ca15 => 15 | .ca16 => 16

end CausalGeometry.Program
