Require Import Nijn.Nijn.
Open Scope poly_scope.


Inductive base_types := 
| Ca  
| Cb  
| Cc.
Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.


Definition a := 
Base Ca.
Definition b := 
Base Cb.
Definition c := 
Base Cc.



Inductive fun_symbols := 
| Tand  
| Tcons  
| Tfalse  
| TFORALL  
| Tforsome  
| Tnil  
| Tor  
| Ttrue.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
match fn_symbols with
  | Tand  =>  c ⟶ c ⟶ c
  | Tcons  =>  a ⟶ b ⟶ b
  | Tfalse  =>  c
  | TFORALL  =>  (a ⟶ c) ⟶ b ⟶ c
  | Tforsome  =>  (a ⟶ c) ⟶ b ⟶ c
  | Tnil  =>  b
  | Tor  =>  c ⟶ c ⟶ c
  | Ttrue => c
end.
Definition and {C} : tm fn_arity C _ := 
BaseTm Tand.
Definition cons {C} : tm fn_arity C _ := 
BaseTm Tcons.
Definition false {C} : tm fn_arity C _ := 
BaseTm Tfalse.
Definition FORALL {C} : tm fn_arity C _ := 
BaseTm TFORALL.
Definition forsome {C} : tm fn_arity C _ := 
BaseTm Tforsome.
Definition nil {C} : tm fn_arity C _ := 
BaseTm Tnil.
Definition or {C} : tm fn_arity C _ := 
BaseTm Tor.
Definition true {C} : tm fn_arity C _ := 
BaseTm Ttrue.



Program Definition rule_0 := 
    make_rewrite
    (∙) _
    (and · true · true)
    true.
Program Definition rule_1 := 
    make_rewrite
    (_ ,, ∙) _
    (and ·  V 0 · false)
    false.
Program Definition rule_2 := 
    make_rewrite
    (_ ,, ∙) _
    (and · false ·  V 0)
    false.
Program Definition rule_3 := 
    make_rewrite
    (_ ,, ∙) _
    (or · true ·  V 0)
    true.
Program Definition rule_4 := 
    make_rewrite
    (_ ,, ∙) _
    (or ·  V 0 · true)
    true.
Program Definition rule_5 := 
    make_rewrite
    (∙) _
    (or · false · false)
    false.
Program Definition rule_6 := 
    make_rewrite
    (_ ,, ∙) _
    (FORALL ·  V 0 · nil)
    true.
Program Definition rule_7 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (FORALL ·  V 0 · (cons ·  V 1 ·  V 2))
    (and · ( V 0 ·  V 1) · (FORALL ·  V 0 ·  V 2)).
Program Definition rule_8 := 
    make_rewrite
    (_ ,, ∙) _
    (forsome ·  V 0 · nil)
    false.
Program Definition rule_9 := 
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (forsome ·  V 0 · (cons ·  V 1 ·  V 2))
    (or · ( V 0 ·  V 1) · (forsome ·  V 0 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: rule_2 :: rule_3 :: rule_4 :: rule_5 :: rule_6 :: rule_7 :: rule_8 :: rule_9 :: List.nil).


Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
match fn_symbols with
| Tand  => 
 λP
λP
(to_Poly (P_const 2))
| Tcons  => 
 λP let y0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 3 + P_const 3 * y0 + P_const 3 * y0 * y1 + P_const 3 * y1))
| Tfalse  => 
 (to_Poly (P_const 0))
| TFORALL  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 2 * y1 + P_const 3 * y1 * (G0 ·P (y1))))
| Tforsome  => 
 λP let G0 := P_var (Vs Vz) in
λP let y1 := P_var Vz in
(to_Poly (P_const 2 * y1 + P_const 2 * (G0 ·P (y1)) + P_const 3 * y1 * (G0 ·P (y1))))
| Tnil  => 
 (to_Poly (P_const 3))
| Tor  => 
 λP
λP
(to_Poly (P_const 1))
| Ttrue => 
(to_Poly (P_const 0))
end.
Definition  trs_isSN : isSN trs.
Proof.
solve_poly_SN map_fun_poly.
Qed.
