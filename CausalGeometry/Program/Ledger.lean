import CausalGeometry.Program.Campaign

namespace CausalGeometry.Program

/-- Number of atomic obligations assigned to each gate. -/
def Campaign.rows : Campaign → Nat
  | .ca00 => 12
  | .ca01 => 14
  | .ca02 => 16
  | .ca03 => 18
  | .ca04 => 14
  | .ca05 => 18
  | .ca06 => 18
  | .ca07 => 16
  | .ca08 => 18
  | .ca09 => 24
  | .ca10 => 18
  | .ca11 => 22
  | .ca12 => 20
  | .ca13 => 24
  | .ca14 => 16
  | .ca15 => 12
  | .ca16 => 20

def coreRows : Nat := 186
def eciaRows : Nat := 82
def closureRows : Nat := 12
def wilderberRows : Nat := 20
def totalRows : Nat := 300

example : coreRows + eciaRows + closureRows + wilderberRows = totalRows := by
  decide

end CausalGeometry.Program
