open TypesCommon

module type Env = sig
  type t
  type sail_value  
  val empty : unit -> t

  val get_var : t -> string -> sailtype * sail_value
  val declare_var : t -> string -> sailtype * sail_value -> t
  val print_env : t -> unit

end

module type StackEnv = 
sig
  include Env
  type frame
  val push_frame :  t -> frame -> t
  val pop_frame : t -> t

  val new_frame : t -> t
  val current_frame : t -> frame * t
end