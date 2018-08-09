(* JsCoq/SerAPI
 *
 * Copyright (C) 2016-2018 Emilio J. Gallego Arias
 * Copyright (C) 2016-2018 Mines ParisTech
 *
 * LICENSE: GPLv3+
 *)

(* Library management for JsCoq

   Due to the large size of Coq libraries, we wnat to perform caching
   and lazy loading in the browser.
*)
open Jslib
open Lwt
open Js

let cma_verb     = false
let pkg_prefix   = ref ""
let coq_pkgs_dir = "coq-pkgs/"

(* Main file_cache, indexed by url*)
type cache_entry = {
  (* vo_content is backed by a TypedArray now *)
  file_content : string;
  md5        : Digest.t;
}

(* Number of actual files ~ 2000 *)
let file_cache : (string, cache_entry) Hashtbl.t = Hashtbl.create 503

(* The cma resolving cache maps a cma module to its actual path. *)
let cma_cache : (string, string) Hashtbl.t = Hashtbl.create 103

(* XXX This should be the serialization of the jslib.ml:coq_pkg, but
   waiting for JSON support *)
class type pkgInfo = object
  method name        : js_string t writeonly_prop
  method desc        : js_string t writeonly_prop
  method no_files_   : int         writeonly_prop
end

class type bundleInfo = object
  method desc        : js_string t            writeonly_prop
  method deps        : js_string t js_array t writeonly_prop
  method pkgs        : pkgInfo   t js_array t writeonly_prop
end

class type progressInfo = object
  method bundle_name_ : js_string t writeonly_prop
  method pkg_name_    : js_string t writeonly_prop
  method loaded       : int         writeonly_prop
  method total        : int         writeonly_prop
end

let mk_pkgInfo pkg : pkgInfo t =
  let pi      = Js.Unsafe.obj [||]   in
  pi##.name      := string @@ to_dir  pkg;
  pi##.desc      := string @@ to_desc pkg;
  pi##.no_files_ := no_files pkg;
  pi


let build_bundle_info bundle : bundleInfo t =
  let bi      = Js.Unsafe.obj [||]   in
  let bi_deps = Js.array @@ Array.of_list @@ List.map Js.string  bundle.deps in
  let bi_pkgs = Js.array @@ Array.of_list @@ List.map mk_pkgInfo bundle.pkgs in
  bi##.desc := string bundle.desc;
  bi##.deps := bi_deps;
  bi##.pkgs := bi_pkgs;
  bi

let mk_progressInfo bundle pkg number =
  let pi           = Js.Unsafe.obj [||]   in
  pi##.bundle_name_ := string bundle;
  pi##.pkg_name_    := string @@ to_dir pkg;
  pi##.total        := no_files pkg;
  pi##.loaded       := number;
  pi

(* Global Callbacks *)
type pkg_callbacks = {
  bundle_info     : bundleInfo t -> unit;
  bundle_start    : bundleInfo t -> unit;
  bundle_load     : bundleInfo t -> unit;
  pkg_start    : progressInfo t -> unit;
  pkg_progress : progressInfo t -> unit;
  pkg_load     : progressInfo t -> unit;
}

let cb : pkg_callbacks ref = ref {
  bundle_info  = (fun _ -> ());
  bundle_start = (fun _ -> ());
  bundle_load  = (fun _ -> ());
  pkg_start    = (fun _ -> ());
  pkg_progress = (fun _ -> ());
  pkg_load     = (fun _ -> ());
  }

let preload_vo_file ?(refresh=false) base_url (file, _hash) : unit Lwt.t =
  let open XmlHttpRequest                           in
  let open Lwt_xmlHttpRequest                       in
  (* Jslog.printf Jslog.jscoq_log "Start preload file %s\n%!" name; *)
  let full_url    = base_url  ^ "/" ^ file          in
  let request_url = !pkg_prefix ^ full_url          in
  let cached      = Hashtbl.mem file_cache full_url in

  (* Only reload if not cached or a refresh is requested *)
  if not cached || refresh then begin
  perform_raw ~response_type:ArrayBuffer request_url >>= fun frame ->
  (* frame.code contains the request status *)
  (* Is this redudant with the Opt check? I guess so *)
  if frame.code = 200 || frame.code = 0 then
    Js.Opt.case
      frame.content
      (fun ()        -> ())
      (fun raw_array ->
         (* Thanks to @hhugo *)
         let vo_s = Typed_array.String.of_arrayBuffer raw_array in
         let cache_entry = {
           file_content = vo_s;
           md5          = Digest.string "";
           (* md5        = Digest.string vo_s; *)
           (* We used to do the md5 in the past, or we would eat memory too
            * fast, the GC won't fire up, and the browser would crash!
            * Misteries of JavaScript! Anyways, md5 is useful to debug
            * downloads.
            *)
         } in
         if cma_verb then Format.eprintf "Cached: %s with md5: %s\n%!" full_url (Digest.to_hex cache_entry.md5);
         Hashtbl.add file_cache full_url cache_entry;
         ()
         (* Jslog.printf Jslog.jscoq_log "Cached %s [%d/%d/%d/%s]\n%!" full_url bl (u8arr##length)
          *         (cache_entry.vo_content##length) (Digest.to_hex cache_entry.md5)
          *)
      );
  Lwt.return_unit
  end
  else Lwt.return_unit

(* We grab the `cma/cmo`.js version of the module, we also add it
   to the path resolution cache: *)
let preload_cma_file base_url (file, _hash) : unit Lwt.t =
  let js_file = file ^ ".js"                in
  preload_vo_file base_url (js_file, _hash) >>= fun () ->
  if cma_verb then Format.eprintf "pre-loading cma file (%s, %s)\n%!" base_url js_file;
  Hashtbl.add cma_cache file base_url;
  Lwt.return_unit

let preload_pkg ?(verb=false) bundle pkg : unit Lwt.t =
  let pkg_dir = to_dir pkg                                           in
  let ncma    = List.length pkg.cma_files                            in
  let nfiles  = no_files pkg                                         in
  if verb then
    Format.eprintf "pre-loading package %s, [00/%02d] files\n%!" pkg_dir nfiles;
  !cb.pkg_start (mk_progressInfo bundle pkg 0);
  let preload_vo_and_log nc i f =
    preload_vo_file pkg_dir f >>= fun () ->
    if verb then
      Format.eprintf "pre-loading package %s, [%02d/%02d] files\n%!" pkg_dir (i+nc+1) nfiles;
    !cb.pkg_progress (mk_progressInfo bundle pkg (i+nc+1));
    Lwt.return_unit
  in
  Lwt_list.iter_s (preload_cma_file pkg_dir) pkg.cma_files    >>= fun () ->
  Lwt_list.iteri_s (preload_vo_and_log ncma) pkg.vo_files     >>= fun () ->
  Icoq.add_load_path pkg.pkg_id pkg_dir (ncma > 0);
  !cb.pkg_load (mk_progressInfo bundle pkg nfiles);
  Lwt.return_unit

(* Load a bundle *)
let rec preload_from_file ?(verb=false) file =
  let open Lwt_xmlHttpRequest in
  let file_url = !pkg_prefix ^ file ^ ".json" in
  get file_url >>= (fun res ->
  (* XXX: Use _JSON.json??????? *)
  let bundle = (match Jslib.coq_bundle_of_yojson
                     (Yojson.Safe.from_string res.content)
                with
                | Result.Ok bundle -> bundle
                | Result.Error s   -> (Format.eprintf "JSON error in preload_from_file: %s\n%!" s;
                                      raise (Failure "JSON")))
  in
  let bundle_info = build_bundle_info bundle in
  !cb.bundle_start bundle_info;
  (* Load deps *)
  Lwt_list.iter_p (preload_from_file ~verb:verb) bundle.deps <&>
  Lwt_list.iter_p (preload_pkg  ~verb:verb file) bundle.pkgs     >>= fun () ->
  !cb.bundle_load  bundle_info;
  return_unit)

let iter_arr (f : 'a -> unit Lwt.t) (l : 'a js_array t) : unit Lwt.t =
  let f_js = wrap_callback (fun p x _ _ -> f x >>= (fun () -> p)) in
  l##(reduce_init f_js return_unit)

let info_from_file file =
  let open Lwt_xmlHttpRequest in
  let file_url = !pkg_prefix ^ file ^ ".json" in
  get file_url >>= fun res ->
  let bundle = (match Jslib.coq_bundle_of_yojson
                     (Yojson.Safe.from_string res.content)
                with
                | Result.Ok bundle -> bundle
                | Result.Error s   -> (Format.eprintf "JSON error in preload_from_file: %s\n%!" s;
                                       raise (Failure "JSON")))
  in
  return @@ !cb.bundle_info (build_bundle_info bundle)

let init init_callback pkg_cb base_path all_pkgs init_pkgs =
  cb         := pkg_cb;
  pkg_prefix := to_string base_path ^ "/" ^ coq_pkgs_dir;
  Lwt.async (fun () ->
    iter_arr (fun x -> to_string x |> info_from_file)                all_pkgs  >>= fun () ->
    iter_arr (fun x -> to_string x |> preload_from_file ~verb:false) init_pkgs >>= fun () ->
    init_callback ();
    return_unit
  )

let load_pkg pkg_file = Lwt.async (fun () ->
    preload_from_file pkg_file >>= fun () ->
    (* XXX: No notification for bundle loading *)
    (* !cb.bundle_load pkg_file; *)
    return_unit
  )

(* let _is_bad_url _ = false *)

(* XXX: Wait until we have enough UI support for logging *)
let coq_vo_req url =
  if cma_verb then Format.eprintf "file %s requested\n%!" url; (* with category info *)
  (* if not @@ is_bad_url url then *)
  try let c_entry = Hashtbl.find file_cache url in
    (* Jslog.printf Jslog.jscoq_log "coq_resource_req %s\n%!" (Js.to_string url); *)
    Some c_entry.file_content
  with
    (* coq_vo_reg is also invoked throught the Sys.file_exists call
     * in mltop:file_of_name function, a good example on how to be
     * too smart for your own good $:-)
     *
     * Sadly coq only uses this information to determine if it will
     * load a cmo/cma file, not to guess the path...
     *)
  | Not_found ->
    (* We check vs the true filesystem, even if unfortunately the
       cache has to be used in coq_cma_req below :(

       Maybe we can fix this pitfall for 8.7 :/
    *)
    (* Format.eprintf "check path %s\n%!" url; *)
    if Filename.(check_suffix url "cma" || check_suffix url "cmo") then
      let js_file = (url ^ ".js")    in
      (* Format.eprintf "trying %s\n%!" js_file; *)
      try let c_entry = Hashtbl.find file_cache js_file in
        Some c_entry.file_content
      with Not_found -> None
    else None

let coq_cma_req cma =
  let open Format in
  if cma_verb then eprintf "bytecode file %s requested\n%!" cma;
  try
    let cma_path = Hashtbl.find cma_cache cma  in
    (* Now, the js file should be in the file cache *)
    let js_file = cma_path ^ "/" ^ cma ^ ".js" in
    if cma_verb then eprintf "requesting load of %s\n%!" js_file;
    try
      let js_code = Hashtbl.(find file_cache js_file).file_content in
      (* When eval'ed, the js_code will return a closure waiting for the
         jsoo global object to link the plugin.
      *)
      Js.Unsafe.((eval_string ("(" ^ js_code ^ ")") : < .. > Js.t -> unit) global)
    with
    | Not_found ->
      eprintf "cache inconsistecy for %s !! \n%!" cma;
  with
  | Not_found ->
    eprintf "!! bytecode file %s not found in path\n%!" cma
