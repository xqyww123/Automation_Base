theory Automation_Base
  imports HOL.Int
begin

ML_file \<open>default_num_typ.ML\<close>

setup \<open>Context.theory_map (Default_Num_Typ.set (SOME \<^typ>\<open>int\<close>))\<close>

end