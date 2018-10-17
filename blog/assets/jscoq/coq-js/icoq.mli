(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Coq Interface to be used by JavaScript Ocaml code. Parts based in
   the coq source code.

   By Emilio J. Gallego Arias, Mines ParisTech, Paris.
*)

open Feedback

(* Init options for coq *)
type init_opts = {

  (* callback to load cma files *)
  ml_load    : string -> unit;

  (* callback to handle async feedback *)
  fb_handler : feedback -> unit;

}

(** [init opts] Initialize the Coq engine *)
val init : init_opts -> Stateid.t

(** [version] returns miscellaneous version information *)
val version : string * string * string * string

(** [add_load_path qid path has_ml] associate a coq package namespace
    [qid] to a [path], register for ml searching *)
val add_load_path : string list -> string -> bool -> unit

(** [add_to_doc sid eid cmd] Add [cmd] to the doc [sid] with edit_id
    [eid] and returns the new doc's stateid. Note that [add_to_doc] doesn't
    force Coq to process the new parts of the document, see [commit] *)
val add_to_doc : Stateid.t -> string -> Stateid.t

(** [edit_doc sid] moves the tip of the document to [sid], discarding
    all edits added after [sid] *)
val edit_doc : Stateid.t -> unit

(** [commit sid] commit the changes to the current document. It will
    produce an exception in case of error. *)
val commit_doc : Stateid.t -> unit

(** [query sid cmd] Executes a command without changing the state. *)
val query : Stateid.t -> string -> unit

(** [string_or_goals ()] returns a string representing the current goals  *)
val string_of_goals : unit -> string

(** [set_debug t] enables/disables debug mode  *)
val set_debug : bool -> unit

module Options : sig
  type 'a t

  (* Printing depth *)
  val print_width  : int  t

  (** [set_bool_option opt val] Sets bool option to val. *)
  val set_bool_option : bool t -> bool -> unit

  (** [set_int_option opt val] Sets integer option to val. *)
  val set_int_option : int t -> int -> unit
end
