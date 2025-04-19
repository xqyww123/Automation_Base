signature DEFAULT_NUM_TYP = sig

val get: Context.generic -> typ option
val map: (typ option -> typ option) -> Context.generic -> Context.generic
val set: typ option -> Context.generic -> Context.generic

end

structure Default_Num_Typ : DEFAULT_NUM_TYP = struct

structure Data = Generic_Data (
type T = typ option
val empty = NONE
val merge = merge_options
)

fun chk_term ctxt tm =
  let val thy = Proof_Context.theory_of ctxt
      val subsort = Sign.subsort thy
      fun qchk'S S = exists (fn S' => subsort (S, S')) [\<^sort>\<open>numeral\<close>, \<^sort>\<open>one\<close>, \<^sort>\<open>zero\<close>]
      fun qchk'T (TFree (_, s)) = qchk'S s
        | qchk'T (TVar  (_, s)) = qchk'S s
        | qchk'T _ = false
      val qchk' = exists_subtype qchk'T
      val qchk = exists_subterm (fn Const (_, T) => qchk' T
                                  | Free  (_, T) => qchk' T
                                  | Var   (_, T) => qchk' T
                                  | _ => false)

      val num_ty = Data.get (Context.Proof ctxt)
      fun convert tm =
        let val subs = fold_types (fold_atyps (fn T =>
                  if qchk'T T then AList.update (op =) (T, the num_ty) else I)) tm []
         in subst_atomic_types subs tm
        end
   in if is_some num_ty andalso qchk tm
    then convert tm
    else tm
  end

val _ = Theory.setup (Context.theory_map (
  Syntax_Phases.term_check 1000 "default numeral type" (map o chk_term)))


val set = Data.put
val get = Data.get
val map = Data.map

end