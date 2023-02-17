Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Cboolean  
| Clist  
| Cnat.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition boolean := 
Base Cboolean.
Definition list := 
Base Clist.
Definition nat := 
Base Cnat.



Inductive fun_symbols := 
| Tbool  
| Tcons  
| TconsIF  
| Tfalse  
| Tfilter  
| Tnil  
| Trand  
| Ts  
| Ttrue  
| Tzero.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tbool  =>  nat ⟶ boolean
  | Tcons  =>  nat ⟶ list ⟶ list
  | TconsIF  =>  boolean ⟶ nat ⟶ list ⟶ list
  | Tfalse  =>  boolean
  | Tfilter  =>  (nat ⟶ boolean) ⟶ list ⟶ list
  | Tnil  =>  list
  | Trand  =>  nat ⟶ nat
  | Ts  =>  nat ⟶ nat
  | Ttrue  =>  boolean
  | Tzero => nat
end.
Definition bool {C} : tm fn_arity C _ := 
BaseTm Tbool.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition consIF {C} : tm fn_arity C _ := 
BaseTm TconsIF.
Definition false {C} : tm fn_arity C _ := 
BaseTm Tfalse.
Definition filter {C} : tm fn_arity C _ := 
BaseTm Tfilter.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition rand {C} : tm fn_arity C _ := 
BaseTm Trand.
Definition s {C} : tm fn_arity C _ := 
BaseTm Ts.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.
Definition zero {C} : tm fn_arity C _ := 
BaseTm Tzero.



Program Definition rule_0 := 
    make_rewrite
    (_ ,, ∙) _
    (rand ·  V 0)
     V 0.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, ∙) _
    (rand · (s ·  V 0))
    (rand ·  V 0).
Program Definition rule_2 := 
    make_rewrite
    (∙) _
    (bool · zero)
    false.
Program Definition rule_3 := 
    make_rewrite
    (∙) _
    (bool · (s · zero))
    true.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (filter ·  V 0 · nil)
    nil.
Program Definition rule_5 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (filter ·  V 0 · (cons ·  V 1 ·  V 2))
    (consIF · ( V 0 ·  V 1) ·  V 1 · (filter ·  V 0 ·  V 2)).
Program Definition rule_6 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (consIF · true ·  V 0 ·  V 1)
    (cons ·  V 0 ·  V 1).
Program Definition rule_7 := 
    make_rewrite
    (_ ,, _ ,, ∙) _
    (consIF · false ·  V 0 ·  V 1)
     V 1.

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tbool  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 2 * y1 + P_const 3 * y0 + P_const 3 * y0 * y1))
| TconsIF  => 
 λP
λP let y1 := P_var (Vs Vz) in
λP let y2 := P_var Vz in
(to_Poly (P_const 2 + P_const 2 * y2 + P_const 3 * y1 + P_const 3 * y1 * y2))
| Tfalse  => 
 (to_Poly (P_const 1))
| Tfilter  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 1 + y1 + P_const 2 * y1 * (G0 ·P (y1))))
| Tnil  => 
 (to_Poly (P_const 3))
| Trand  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Ts  => 
 λP let y0 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0))
| Ttrue  => 
 (to_Poly (P_const 2))
| Tzero => 
(to_Poly (P_const 3))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
