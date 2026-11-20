Raw benchmark data for the evaluation in "Treesets: Efficient Finite Sets with
Unique Representations" (Grant Jurgensen, ACL2 Workshop 2026).

- `bench-raw.csv`: `(treeset-bench::run-full)`, from
  `[books]/kestrel/data/treeset/benchmark/`. The library has since been
  renamed: the suite is now `(tset-bench::run-full)`, in
  `[books]/kestrel/data/tset/benchmark/`.
- `hash-bench-raw.csv`: `(hash-bench::run-full)`, from
  `[books]/kestrel/data/hash/benchmark/`.
- `reports.txt`: the treap depth and serialized-size reports, which the
  treeset suite prints instead of writing to its CSV.

The libraries have changed since these runs (August 2026), so rerunning
against current books need not reproduce these numbers. The git revision in
the CSV headers, b674f3ee8c, was later rebased as 78d33d3aa8;
books/kestrel/data is identical at the two.

The implementations are in the community books:

- `[books]/kestrel/data/tset/`
- `[books]/kestrel/data/tmap/`
- `[books]/kestrel/data/hash/`
- `[books]/kestrel/data/benchmark/`
