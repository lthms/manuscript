Hinv : inv a
=========================================================================
inv (update_cache_content
       (if cache_hit_dec (cache a) pa
        then a
        else
          update_cache_content
            (if cache_location_is_dirty_dec (cache a) pa
             then
               update_memory_content
                 a
                 (phys_to_hard a (cache_location_address (cache a) pa))
                 (find_in_cache_location (cache a) pa)
             else a)
            pa
            (find_memory_content a (phys_to_hard a pa))) pa
       (context (proc a)))