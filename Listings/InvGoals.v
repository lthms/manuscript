Hreq : hardware_req a
Heqa_2 : a_2 =
         update_memory_content
           a
           (phys_to_hard a (cache_location_address (cache a) pa))
           (find_in_cache_location (cache a) pa)
=========================================================================
hardware_req a_2