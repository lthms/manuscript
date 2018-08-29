Hreq : hardware_req a
(* -- >8 -- *)
Heqa_4 : a_4 =
         update_cache_content a_3
                              pa
                              (find_memory_content a (phys_to_hard a pa))
(* -- >8 -- *)
=========================================================================
hardware_req a_4