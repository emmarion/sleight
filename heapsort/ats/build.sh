#!/bin/sh
set -e
cd "$(dirname "$0")"
patscc -O2 -D_GNU_SOURCE -DATS_MEMALLOC_LIBC -o driver driver.c heapsort_c.c cert_entry.dats heapsort_plain.dats
rm -f ./*_dats.c
