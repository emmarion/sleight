(let ((many r)) (slot-eq vacant-slot vacant-slot))
(comptime-match many r (ENone _))
r
