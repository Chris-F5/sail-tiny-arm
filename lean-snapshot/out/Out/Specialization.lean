import Sail
import Out.Defs
import Sail.ConcurrencyInterfaceV1

namespace Sail.ConcurrencyInterfaceV1

@[simp_sail]
def sailTryCatch (e : SailM α) (h : exception → SailM α) : SailM α := PreSail.ConcurrencyInterfaceV1.sailTryCatch e h

@[simp_sail]
def sailThrow (e : exception) : SailM α := PreSail.ConcurrencyInterfaceV1.sailThrow e

abbrev undefined_unit (_ : Unit) : SailM Unit := PreSail.ConcurrencyInterfaceV1.undefined_unit ()

abbrev undefined_bit (_ : Unit) : SailM (BitVec 1) := PreSail.ConcurrencyInterfaceV1.undefined_bit ()

abbrev undefined_bool (_ : Unit) : SailM Bool := PreSail.ConcurrencyInterfaceV1.undefined_bool ()

abbrev undefined_int (_ : Unit) : SailM Int := throw Error.InfiniteNondeterminisim

abbrev undefined_range (low high : Int) : SailM Int := PreSail.ConcurrencyInterfaceV1.undefined_range low high

abbrev undefined_nat (_ : Unit) : SailM Nat := throw Error.InfiniteNondeterminisim

abbrev undefined_string (_ : Unit) : SailM String := throw Error.InfiniteNondeterminisim

abbrev undefined_bitvector (n : Nat) : SailM (BitVec n) := PreSail.ConcurrencyInterfaceV1.undefined_bitvector n

/-
 - archsem-lean change: I dont understand what this is for? The current implementation
 - just returns a vector of `n` `a`'s.
 -/
-- abbrev undefined_vector (n : Nat) (a : α) : SailM (Vector α n) := PreSail.undefined_vector n a

abbrev internal_pick {α : Type} : List α → SailM α := PreSail.ConcurrencyInterfaceV1.internal_pick

abbrev writeReg (reg : Register) (v : RegisterType reg) : SailM PUnit := PreSail.ConcurrencyInterfaceV1.writeReg reg v

abbrev readReg (reg : Register) : SailM (RegisterType reg) := PreSail.ConcurrencyInterfaceV1.readReg reg

abbrev RegisterRef := @PreSail.ConcurrencyInterfaceV1.RegisterRef Register RegisterType

abbrev readRegRef (reg_ref : RegisterRef α) : SailM α := PreSail.ConcurrencyInterfaceV1.readRegRef reg_ref

abbrev writeRegRef (reg_ref : RegisterRef α) (a : α) : SailM Unit := PreSail.ConcurrencyInterfaceV1.writeRegRef reg_ref a

abbrev reg_deref (reg_ref : RegisterRef α) : SailM α := PreSail.ConcurrencyInterfaceV1.reg_deref reg_ref

abbrev assert (p : Bool) (s : String) : SailM Unit := PreSail.ConcurrencyInterfaceV1.assert p s


abbrev sail_mem_write [Arch] (req : Mem_write_request n vasize (BitVec pa_size) ts arch) : SailM (Result (Option Bool) Arch.abort) :=
  PreSail.ConcurrencyInterfaceV1.sail_mem_write req

abbrev write_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) (value : BitVec (8 * data_size)) :
    SailM Unit := PreSail.ConcurrencyInterfaceV1.write_ram addr_size data_size _hex_ram addr value

abbrev sail_mem_read [Arch] (req : Mem_read_request n vasize (BitVec pa_size) ts arch) : SailM (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) := PreSail.ConcurrencyInterfaceV1.sail_mem_read req

abbrev read_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) : SailM (BitVec (8 * data_size)) := PreSail.ConcurrencyInterfaceV1.read_ram addr_size data_size _hex_ram addr

abbrev sail_barrier (a : α) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_barrier a

abbrev sail_cache_op [Arch] (op : Arch.cache_op) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_cache_op op
abbrev sail_tlbi [Arch] (op : Arch.tlb_op) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_tlbi op
abbrev sail_translation_start [Arch] (ts : Arch.trans_start) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_translation_start ts
abbrev sail_translation_end [Arch] (te : Arch.trans_end) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_translation_end te
abbrev sail_take_exception [Arch] (f : Arch.fault) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_take_exception f
abbrev sail_return_exception [Arch] (a : Arch.pa) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_return_exception a


abbrev cycle_count (a : Unit) : SailM Unit := PreSail.ConcurrencyInterfaceV1.cycle_count a

abbrev get_cycle_count (a : Unit) : SailM Nat := PreSail.ConcurrencyInterfaceV1.get_cycle_count a


abbrev print_effect (str : String) : SailM Unit := PreSail.ConcurrencyInterfaceV1.print_effect str

abbrev print_int_effect (str : String) (n : Int) : SailM Unit := PreSail.ConcurrencyInterfaceV1.print_int_effect str n

abbrev print_bits_effect {w : Nat} (str : String) (x : BitVec w) : SailM Unit := PreSail.ConcurrencyInterfaceV1.print_bits_effect str x

abbrev print_endline_effect (str : String) : SailM Unit := PreSail.ConcurrencyInterfaceV1.print_endline_effect str

def SailME.run (m : SailME α α) : SailM α := PreSail.ConcurrencyInterfaceV1.PreSailME.run m

def SailME.throw (e : α) : SailME α β := PreSail.ConcurrencyInterfaceV1.PreSailME.throw e

abbrev sailTryCatchE (e : SailME β α) (h : exception → SailME β α) : SailME β α := PreSail.ConcurrencyInterfaceV1.sailTryCatchE e h

end Sail.ConcurrencyInterfaceV1


namespace Sail.ConcurrencyInterfaceV2

/-
 - archsem-lean change: `open ArchSem` instead of `PreSail.ConcurrencyInterfaceV2`
 - If we opened `PreSail.ConcurrencyInterfaceV2`, we would get naming conflicts with
 - the namespace we are defining here.
 -/
open ArchSem

/-
 - archsem-lean change: These functions were in `Sail` but are moved into
 - `Sail.ConcurrencyInterfaceV2` since they are now interface specific.
 - We also need to replace many occurances of `PreSail` with `PreSail.ConcurrencyInterfaceV2`.
 -/
@[simp_sail]
def sailTryCatch (e : SailM α) (h : exception → SailM α) : SailM α := PreSail.ConcurrencyInterfaceV2.sailTryCatch e h

@[simp_sail]
def sailThrow (e : exception) : SailM α := PreSail.ConcurrencyInterfaceV2.sailThrow e

abbrev undefined_unit (_ : Unit) : SailM Unit := PreSail.ConcurrencyInterfaceV2.undefined_unit ()

abbrev undefined_bit (_ : Unit) : SailM (BitVec 1) := PreSail.ConcurrencyInterfaceV2.undefined_bit ()

abbrev undefined_bool (_ : Unit) : SailM Bool := PreSail.ConcurrencyInterfaceV2.undefined_bool ()

abbrev undefined_int (_ : Unit) : SailM Int := throw Error.InfiniteNondeterminisim

abbrev undefined_range (low high : Int) : SailM Int := PreSail.ConcurrencyInterfaceV2.undefined_range low high

abbrev undefined_nat (_ : Unit) : SailM Nat := throw Error.InfiniteNondeterminisim

abbrev undefined_string (_ : Unit) : SailM String := throw Error.InfiniteNondeterminisim

abbrev undefined_bitvector (n : Nat) : SailM (BitVec n) := PreSail.ConcurrencyInterfaceV2.undefined_bitvector n

/-
 - archsem-lean change: I dont understand what this is for? The current implementation
 - just returns a vector of `n` `a`'s.
 -/
-- abbrev undefined_vector (n : Nat) (a : α) : SailM (Vector α n) := PreSail.undefined_vector n a

abbrev internal_pick {α : Type} : List α → SailM α := PreSail.ConcurrencyInterfaceV2.internal_pick

abbrev writeReg (reg : Register) (v : RegisterType reg) : SailM PUnit := PreSail.ConcurrencyInterfaceV2.writeReg reg v

abbrev readReg (reg : Register) : SailM (RegisterType reg) := PreSail.ConcurrencyInterfaceV2.readReg reg

/- archsem-lean change: `Register RegisterType` are no longer passed to RegisterRef. -/
abbrev RegisterRef := @PreSail.ConcurrencyInterfaceV2.RegisterRef

abbrev readRegRef (reg_ref : RegisterRef α) : SailM α := PreSail.ConcurrencyInterfaceV2.readRegRef reg_ref

abbrev writeRegRef (reg_ref : RegisterRef α) (a : α) : SailM Unit := PreSail.ConcurrencyInterfaceV2.writeRegRef reg_ref a

abbrev reg_deref (reg_ref : RegisterRef α) : SailM α := PreSail.ConcurrencyInterfaceV2.reg_deref reg_ref

abbrev assert (p : Bool) (s : String) : SailM Unit := PreSail.ConcurrencyInterfaceV2.assert p s

abbrev sail_mem_read [Arch] (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) :
    SailM (Result ((Vector (BitVec 8) n) × (Vector Bool nt)) Arch.abort) :=
  PreSail.ConcurrencyInterfaceV2.sail_mem_read req

def sail_mem_write [Arch] (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) (valueBytes : Vector (BitVec 8) n) (tags : Vector Bool nt) :
    SailM (Result (Option Bool) Arch.abort) := do
  PreSail.ConcurrencyInterfaceV2.sail_mem_write req valueBytes tags

abbrev sail_sys_reg_read [Arch] (id : Arch.sys_reg_id) (r : RegisterRef α) : SailM α :=
  PreSail.ConcurrencyInterfaceV2.sail_sys_reg_read id r

abbrev sail_sys_reg_write [Arch] (id : Arch.sys_reg_id) (r : RegisterRef α) (v : α) : SailM Unit :=
  PreSail.ConcurrencyInterfaceV2.sail_sys_reg_write id r v

abbrev sail_mem_address_announce [Arch] (ann : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) : SailM Unit :=
  PreSail.ConcurrencyInterfaceV2.sail_mem_address_announce ann

abbrev sail_barrier [Arch] (b : Arch.barrier) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_barrier b
abbrev sail_cache_op [Arch] (op : Arch.cache_op) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_cache_op op
abbrev sail_tlbi [Arch] (op : Arch.tlbi) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_tlbi op
abbrev sail_translation_start [Arch] (ts : Arch.trans_start) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_translation_start ts
abbrev sail_translation_end [Arch] (te : Arch.trans_end) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_translation_end te
abbrev sail_take_exception [Arch] (f : Arch.exn) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_take_exception f
abbrev sail_return_exception (a : Unit) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_return_exception a

abbrev cycle_count (a : Unit) : SailM Unit := PreSail.ConcurrencyInterfaceV2.cycle_count a

abbrev get_cycle_count (a : Unit) : SailM Nat := PreSail.ConcurrencyInterfaceV2.get_cycle_count a


abbrev print_effect (str : String) : SailM Unit := PreSail.ConcurrencyInterfaceV2.print_effect str

abbrev print_int_effect (str : String) (n : Int) : SailM Unit := PreSail.ConcurrencyInterfaceV2.print_int_effect str n

abbrev print_bits_effect {w : Nat} (str : String) (x : BitVec w) : SailM Unit := PreSail.ConcurrencyInterfaceV2.print_bits_effect str x

abbrev print_endline_effect (str : String) : SailM Unit := PreSail.ConcurrencyInterfaceV2.print_endline_effect str

def SailME.run (m : SailME α α) : SailM α := PreSail.ConcurrencyInterfaceV2.PreSailME.run m

def SailME.throw (e : α) : SailME α β := PreSail.ConcurrencyInterfaceV2.PreSailME.throw e

abbrev sailTryCatchE (e : SailME β α) (h : exception → SailME β α) : SailME β α := PreSail.ConcurrencyInterfaceV2.sailTryCatchE e h

/-
 - archsem-lean change: I'm not sure exactly what this unwrapValue is here for, but
 - I dont believe we are able to support running the free monad without an interpreter.
 -/
-- def unwrapValue [Inhabited α] (x : SailM α) : α :=
--   match x.run default with
--   | .ok x _ => x
--   | _ => default

end Sail.ConcurrencyInterfaceV2
