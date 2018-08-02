Hreq : hardware_req a
Heqa_2 : a_2 =
         update_memory_content
           a
           (phys_to_hard a (cache_location_address (cache a) pa))
           (find_in_cache_location (cache a) pa)
Heqa_3 : a_3 = (if cache_location_is_dirty_dec (cache a) pa
                then a_2
                else a)
Heqa_4 : a_4 =
         update_cache_content a_3
                              pa
                              (find_memory_content a (phys_to_hard a pa))
Heqa_5 : a_5 = (if cache_hit_dec (cache a) pa
                then a
                else a_4)
Heqa_6 : a_6 = update_cache_content a_5 pa (context (proc a))
=========================================================================
hardware_req a_6