# test-stat-replicant-1 and test-stat-replicant-2 are left out from
# this list for reasons explained in a comment below.
TEST:= test-cp-replicant-1 test-cp-replicant-2 test-cp-replicant-3 \
test-cp-replicant-4 mtools-test-cp-replicant-2 \
test-mkfs-replicant-1 test-mkfs-replicant-2 \
test-wc-replicant-1 test-wc-replicant-2 test-wc-replicant-3 \
test-rm-replicant-1 test-rm-replicant-2 test-rm-replicant-3 \
mtools-test-rm-replicant-1 \
test-unlink-replicant-1 test-unlink-replicant-2 \
test-unlink-replicant-3 \
test-mkdir-replicant-1 test-mkdir-replicant-2 \
mtools-test-mkdir-replicant-1 \
test-rmdir-replicant-1 test-rmdir-replicant-2 \
mtools-test-rmdir-replicant-1 \
test-mv-replicant-1 mtools-test-mv-replicant-1 \
mtools-test-mv-replicant-2 \
test-ls-replicant-1 \
test-truncate-replicant-1 test-truncate-replicant-2 # test-rm-replicant-4 mtools-test-rm-replicant-2

test: $(TEST)

.PHONY: clean-mountpoint test clean $(TEST)

.PHONY: debug-create-dir-and-file debug-create-dir debug-do-nothing \
debug-create-dir-copy-file

.PHONY: mtools-read-write-test-128MB \
mtools-read-write-test-256MB \
mtools-read-write-test-512MB mtools-read-write-test-1024MB

# FUSEPOINT and BBFS are commented below because they refer to Joseph
# Pfeiffer's pedagogical Big Brother Filesystem, which I used in some
# of the tests. For almost every test, they only helped log the
# syscalls and their return values without affecting the course of the
# test; however, the stat tests test-stat-replicant-1 and
# test-stat-replicant-2 do rely on them. Without the interposition of
# the FUSE layer, the id value in the struct statfs can be completely
# arbitrary depending on mount time details which our stat
# implementation has no access to, but when FUSE is interposed, a 0
# value is assigned to id. This value is hard-coded in the stat
# tests; they can be run by downloading and compiling BBFS
# (https://www.cs.nmsu.edu/~pfeiffer/fuse-tutorial/) and noting the
# path to the executable in the BBFS variable, below.
DISK=disk1.raw
SIZE=70000
MOUNTPOINT=mount1
# FUSEPOINT=mount2
# BBFS=$(HOME)/src/bbfs/fuse-tutorial-2018-02-04/src/bbfs
UID=$(shell id -u)
GID=$(shell id -g)
MTOOLSRC=$(shell pwd)/.mtoolsrc

clean:
	rm -f *output*

clean-mountpoint:
	rm -rf $(MOUNTPOINT)

$(MOUNTPOINT):
	rm -rf $(MOUNTPOINT)
	mkdir -p $(MOUNTPOINT)

# $(FUSEPOINT):
# 	rm -rf $(FUSEPOINT)
# 	mkdir -p $(FUSEPOINT)

test-cp-replicant-1: cp-ref-output-1.txt cp-output-1.txt
	diff -u -i cp-ref-output-1.txt cp-output-1.txt

test-cp-replicant-2: cp-ref-output-2.txt cp-output-2.txt
	diff -u -i cp-ref-output-2.txt cp-output-2.txt

test-cp-replicant-3: cp-ref-output-3.txt cp-output-3.txt
	diff -u -i cp-ref-output-3.txt cp-output-3.txt

test-cp-replicant-4: cp-ref-output-4.txt cp-output-4.txt
	diff -u -i cp-ref-output-4.txt cp-output-4.txt

mtools-test-cp-replicant-2: mtools-cp-ref-output-2.txt mtools-cp-output-2.txt
	diff -u -i mtools-cp-ref-output-2.txt mtools-cp-output-2.txt

test-cp-replicant-5: cp-ref-output-5.txt cp-output-5.txt
	diff -u -i cp-ref-output-5.txt cp-output-5.txt

test-mkfs-replicant-1: mkfs-ref-output-1.txt mkfs-output-1.txt
	diff -u -i mkfs-ref-output-1.txt mkfs-output-1.txt

test-mkfs-replicant-2: mkfs-ref-output-2.txt mkfs-output-2.txt
	diff -u -i mkfs-ref-output-2.txt mkfs-output-2.txt

test-mkfs-replicant-3: mkfs-ref-output-3.txt mkfs-output-3.txt
	diff -u -i mkfs-ref-output-3.txt mkfs-output-3.txt

test-wc-replicant-1: wc-ref-output-1.txt wc-output-1.txt
	diff -u -i wc-ref-output-1.txt wc-output-1.txt

test-wc-replicant-2: wc-ref-output-2.txt wc-output-2.txt
	diff -u -i wc-ref-output-2.txt wc-output-2.txt

test-wc-replicant-3: wc-ref-output-3.txt wc-output-3.txt
	diff -u -i wc-ref-output-3.txt wc-output-3.txt

test-stat-replicant-1: stat-ref-output-1.txt stat-output-1.txt
	diff -u -i stat-ref-output-1.txt stat-output-1.txt

test-stat-replicant-2: stat-ref-output-2.txt stat-output-2.txt
	diff -u -i stat-ref-output-2.txt stat-output-2.txt

test-rm-replicant-1: rm-output-1.raw rm-ref-output-1.raw
	env DISK=$(DISK) REF_INPUT="rm-ref-output-1.raw" \
	INPUT="rm-output-1.raw" $(ACL2) -- < compare-disks.lisp

test-rm-replicant-2: rm-output-2.raw rm-ref-output-2.raw
	env DISK=$(DISK) REF_INPUT="rm-ref-output-2.raw" \
	INPUT="rm-output-2.raw" $(ACL2) -- < compare-disks.lisp

test-rm-replicant-3: rm-output-3.raw rm-ref-output-3.raw
	env DISK=$(DISK) REF_INPUT="rm-ref-output-3.raw" \
	INPUT="rm-output-3.raw" $(ACL2) -- < compare-disks.lisp

test-rm-replicant-4: rm-output-4.raw rm-ref-output-4.raw
	env DISK=$(DISK) REF_INPUT="rm-ref-output-4.raw" \
	INPUT="rm-output-4.raw" $(ACL2) -- < compare-disks.lisp

mtools-test-rm-replicant-1: mtools-rm-ref-output-1.raw mtools-rm-output-1.raw
	env DISK=$(DISK) REF_INPUT="mtools-rm-ref-output-1.raw" \
	INPUT="mtools-rm-output-1.raw" $(ACL2) -- < compare-disks.lisp

mtools-test-rm-replicant-2: mtools-rm-ref-output-2.raw mtools-rm-output-2.raw
	env DISK=$(DISK) REF_INPUT="mtools-rm-ref-output-2.raw" \
	INPUT="mtools-rm-output-2.raw" $(ACL2) -- < compare-disks.lisp

test-unlink-replicant-1: unlink-output-1.raw unlink-ref-output-1.raw
	env DISK=$(DISK) REF_INPUT="unlink-ref-output-1.raw" \
	INPUT="unlink-output-1.raw" $(ACL2) -- < compare-disks.lisp

test-unlink-replicant-2: unlink-output-2.raw unlink-ref-output-2.raw
	env DISK=$(DISK) REF_INPUT="unlink-ref-output-2.raw" \
	INPUT="unlink-output-2.raw" $(ACL2) -- < compare-disks.lisp

test-unlink-replicant-3: unlink-output-3.raw unlink-ref-output-3.raw
	env DISK=$(DISK) REF_INPUT="unlink-ref-output-3.raw" \
	INPUT="unlink-output-3.raw" $(ACL2) -- < compare-disks.lisp

test-mkdir-replicant-1: mkdir-output-1.raw mkdir-ref-output-1.raw
	env DISK=$(DISK) REF_INPUT="mkdir-ref-output-1.raw" \
	INPUT="mkdir-output-1.raw" $(ACL2) -- < compare-disks.lisp

test-mkdir-replicant-2: mkdir-output-2.raw mkdir-ref-output-2.raw
	env DISK=$(DISK) REF_INPUT="mkdir-ref-output-2.raw" \
	INPUT="mkdir-output-2.raw" $(ACL2) -- < compare-disks.lisp

mtools-test-mkdir-replicant-1: mtools-mkdir-ref-output-1.raw mtools-mkdir-output-1.raw
	env DISK=$(DISK) REF_INPUT="mtools-mkdir-ref-output-1.raw" \
	INPUT="mtools-mkdir-output-1.raw" $(ACL2) -- < compare-disks.lisp

mtools-test-mkdir-replicant-2: mtools-mkdir-ref-output-2.raw mtools-mkdir-output-2.raw
	env DISK=$(DISK) REF_INPUT="mtools-mkdir-ref-output-2.raw" \
	INPUT="mtools-mkdir-output-2.raw" $(ACL2) -- < compare-disks.lisp

test-rmdir-replicant-1: rmdir-output-1.raw rmdir-ref-output-1.raw
	env DISK=$(DISK) REF_INPUT="rmdir-ref-output-1.raw" \
	INPUT="rmdir-output-1.raw" $(ACL2) -- < compare-disks.lisp

test-rmdir-replicant-2: rmdir-output-2.raw rmdir-ref-output-2.raw
	env DISK=$(DISK) REF_INPUT="rmdir-ref-output-2.raw" \
	INPUT="rmdir-output-2.raw" $(ACL2) -- < compare-disks.lisp

mtools-test-rmdir-replicant-1: mtools-rmdir-ref-output-1.raw mtools-rmdir-output-1.raw
	env DISK=$(DISK) REF_INPUT="mtools-rmdir-ref-output-1.raw" \
	INPUT="mtools-rmdir-output-1.raw" $(ACL2) -- < compare-disks.lisp

mtools-test-rmdir-replicant-2: mtools-rmdir-ref-output-2.raw mtools-rmdir-output-2.raw
	env DISK=$(DISK) REF_INPUT="mtools-rmdir-ref-output-2.raw" \
	INPUT="mtools-rmdir-output-2.raw" $(ACL2) -- < compare-disks.lisp

test-mv-replicant-1: mv-output-1.raw mv-ref-output-1.raw
	env DISK=$(DISK) REF_INPUT="mv-ref-output-1.raw" \
	INPUT="mv-output-1.raw" $(ACL2) -- < compare-disks.lisp

mtools-test-mv-replicant-1: mtools-mv-output-1.raw mtools-mv-ref-output-1.raw
	env DISK=$(DISK) REF_INPUT="mtools-mv-ref-output-1.raw" \
	INPUT="mtools-mv-output-1.raw" $(ACL2) -- < compare-disks.lisp

mtools-test-mv-replicant-2: mtools-mv-ref-output-2.raw mtools-mv-output-2.raw
	env DISK=$(DISK) REF_INPUT="mtools-mv-ref-output-2.raw" \
	INPUT="mtools-mv-output-2.raw" $(ACL2) -- < compare-disks.lisp

test-ls-replicant-1: ls-ref-output-1.txt ls-output-1.txt
	diff -u -i ls-ref-output-1.txt ls-output-1.txt

test-truncate-replicant-1: truncate-output-1.raw truncate-ref-output-1.raw
	env DISK=$(DISK) REF_INPUT="truncate-ref-output-1.raw" \
	INPUT="truncate-output-1.raw" $(ACL2) -- < compare-disks.lisp

test-truncate-replicant-2: truncate-output-2.raw truncate-ref-output-2.raw
	env DISK=$(DISK) REF_INPUT="truncate-ref-output-2.raw" \
	INPUT="truncate-output-2.raw" $(ACL2) -- < compare-disks.lisp

cp-ref-output-1.txt cp-output-1.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	echo "four" > $(MOUNTPOINT)/vmlinuz
	cat $(MOUNTPOINT)/vmlinuz > cp-ref-output-1.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-1.txt" \
	CP_INPUT="/vmlinuz" $(ACL2) < cp-replicant.lisp

cp-ref-output-2.txt cp-output-2.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt $(MOUNTPOINT)/vmlinuz
	cat $(MOUNTPOINT)/vmlinuz > cp-ref-output-2.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-2.txt" \
	CP_INPUT="/vmlinuz" $(ACL2) < cp-replicant.lisp

cp-ref-output-3.txt cp-output-3.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt $(MOUNTPOINT)/vmlinuz
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	cat $(MOUNTPOINT)/initrd.img > cp-ref-output-3.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-3.txt" \
	CP_INPUT="/initrd.img" $(ACL2) < cp-replicant.lisp

cp-ref-output-4.txt cp-output-4.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt $(MOUNTPOINT)/initrd$$i1.img; \
	done
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	cat $(MOUNTPOINT)/initrd.img > cp-ref-output-4.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-4.txt" \
	CP_INPUT="/initrd.img" $(ACL2) < cp-replicant.lisp

cp-ref-output-5.txt cp-output-5.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt $(MOUNTPOINT)/initrd.img
	sync $(MOUNTPOINT)/initrd.img
	rm $(MOUNTPOINT)/initrd.img
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt $(MOUNTPOINT)/initrd$$i1.img; \
	done
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	cat $(MOUNTPOINT)/initrd.img > cp-ref-output-5.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-5.txt" \
	CP_INPUT="/initrd.img" $(ACL2) < cp-replicant.lisp

mtools-cp-ref-output-2.txt mtools-cp-output-2.txt: cp-replicant.lisp
	rm -f $(DISK) mtools-cp-ref-output-2.txt
	dd if=/dev/zero of=$(DISK) bs=4096 count=17920
	env MTOOLSRC=$(MTOOLSRC) mformat -T 140000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	env MTOOLSRC=$(MTOOLSRC) mcopy c:/vmlinuz mtools-cp-ref-output-2.txt
	env DISK=$(DISK) CP_OUTPUT="mtools-cp-output-2.txt" \
	CP_INPUT="/vmlinuz" $(ACL2) < cp-replicant.lisp

mkfs-ref-output-1.txt mkfs-output-1.txt: $(MOUNTPOINT) \
mkfs.fat-4.1-replicant.lisp
	rm -f $(DISK)
	(mkfs.fat -C -v -F 32 -s 1 $(DISK) $(SIZE)) > mkfs-ref-output-1.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-1.txt" $(ACL2) < \
	mkfs.fat-4.1-replicant.lisp

mkfs-ref-output-2.txt mkfs-output-2.txt: $(MOUNTPOINT) \
mkfs.fat-4.1-replicant.lisp
	rm -f $(DISK)
	(mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)) > mkfs-ref-output-2.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-2.txt" $(ACL2) < \
	mkfs.fat-4.1-replicant.lisp

wc-ref-output-1.txt wc-output-1.txt: $(MOUNTPOINT) wc-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	wc -c < $(MOUNTPOINT)/initrd.img > wc-ref-output-1.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) WC_OUTPUT="wc-output-1.txt" \
	WC_INPUT="/initrd.img" $(ACL2) -- -c < wc-replicant.lisp

wc-ref-output-2.txt wc-output-2.txt: $(MOUNTPOINT) wc-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	wc -l < $(MOUNTPOINT)/initrd.img > wc-ref-output-2.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) WC_OUTPUT="wc-output-2.txt" \
	WC_INPUT="/initrd.img" $(ACL2) -- -l < wc-replicant.lisp

wc-ref-output-3.txt wc-output-3.txt: $(MOUNTPOINT) wc-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	wc -w < $(MOUNTPOINT)/initrd.img > wc-ref-output-3.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) WC_OUTPUT="wc-output-3.txt" \
	WC_INPUT="/initrd.img" $(ACL2) -- -w < wc-replicant.lisp

# stat-ref-output-1.txt stat-output-1.txt: $(MOUNTPOINT) $(FUSEPOINT) stat-replicant.lisp
# 	rm -f $(DISK)
# 	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
# 	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
# 	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
# 	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
# 	cd $(FUSEPOINT); stat -f initrd.img > ../stat-ref-output-1.txt; cd -
# 	sleep 1
# 	fusermount -u $(FUSEPOINT)
# 	sudo umount $(MOUNTPOINT)
# 	env DISK=$(DISK) STAT_OUTPUT="stat-output-1.txt" \
# 	STAT_INPUT="initrd.img" $(ACL2) -- -f < stat-replicant.lisp

# stat-ref-output-2.txt stat-output-2.txt: $(MOUNTPOINT) $(FUSEPOINT) stat-replicant.lisp
# 	rm -f $(DISK)
# 	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
# 	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
# 	$(BBFS) $(MOUNTPOINT) $(FUSEPOINT)
# 	for i1 in $(shell seq 1 32); do \
# 		cp input-1204-bytes.txt $(FUSEPOINT)/initrd$$i1.img; \
# 	done
# 	cp input-4623-bytes.txt $(FUSEPOINT)/initrd.img
# 	cd $(FUSEPOINT); stat -f initrd.img > ../stat-ref-output-2.txt; cd -
# 	sleep 1
# 	fusermount -u $(FUSEPOINT)
# 	sudo umount $(MOUNTPOINT)
# 	env DISK=$(DISK) STAT_OUTPUT="stat-output-2.txt" \
# 	STAT_INPUT="initrd.img" $(ACL2) -- -f < stat-replicant.lisp

rm-ref-output-1.raw rm-output-1.raw: $(MOUNTPOINT) rm-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) rm-ref-output-1.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos rm-ref-output-1.raw $(MOUNTPOINT)
	rm $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RM_OUTPUT="rm-output-1.raw" \
	$(ACL2) -- "/initrd.img" \
	< rm-replicant.lisp

rm-ref-output-2.raw rm-output-2.raw: $(MOUNTPOINT) rm-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt $(MOUNTPOINT)/initrd.img
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt $(MOUNTPOINT)/initrd$$i1.img; \
	done
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) rm-ref-output-2.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos rm-ref-output-2.raw $(MOUNTPOINT)
	rm $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RM_OUTPUT="rm-output-2.raw" \
	$(ACL2) -- "/initrd.img" \
	< rm-replicant.lisp

rm-ref-output-3.raw rm-output-3.raw: $(MOUNTPOINT) rm-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt $(MOUNTPOINT)/initrd.img
	mkdir $(MOUNTPOINT)/tmp
	cp input-1204-bytes.txt $(MOUNTPOINT)/tmp/file.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) rm-ref-output-3.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos rm-ref-output-3.raw $(MOUNTPOINT)
	rm $(MOUNTPOINT)/tmp/file.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RM_OUTPUT="rm-output-3.raw" \
	$(ACL2) -- "/tmp/file.txt" \
	< rm-replicant.lisp

rm-ref-output-4.raw rm-output-4.raw: $(MOUNTPOINT) rm-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt $(MOUNTPOINT)/initrd.img
	mkdir $(MOUNTPOINT)/tmp
	cp input-1204-bytes.txt $(MOUNTPOINT)/tmp/file.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) rm-ref-output-4.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos rm-ref-output-4.raw $(MOUNTPOINT)
	rm -r $(MOUNTPOINT)/tmp
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RM_OUTPUT="rm-output-4.raw" \
	$(ACL2) -- -r "/tmp" \
	< rm-replicant.lisp

mtools-rm-ref-output-1.raw mtools-rm-output-1.raw: rm-replicant.lisp
	rm -f $(DISK) mtools-rm-ref-output-1.raw
	dd if=/dev/zero of=$(DISK) bs=4096 count=17920
	env MTOOLSRC=$(MTOOLSRC) mformat -T 140000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	cp $(DISK) mtools-rm-output-1.raw
	env MTOOLSRC=$(MTOOLSRC) mdel c:/vmlinuz
	cp $(DISK) mtools-rm-ref-output-1.raw
	env DISK="mtools-rm-output-1.raw" RM_OUTPUT="mtools-rm-output-1.raw" \
	$(ACL2) -- "/vmlinuz" < rm-replicant.lisp

mtools-rm-ref-output-2.raw mtools-rm-output-2.raw: rm-replicant.lisp
	rm -f $(DISK) mtools-rm-ref-output-2.raw
	dd if=/dev/zero of=$(DISK) bs=4096 count=17920
	env MTOOLSRC=$(MTOOLSRC) mformat -T 140000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	env MTOOLSRC=$(MTOOLSRC) mmd c:/tmp
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/tmp/file.txt
	cp $(DISK) mtools-rm-output-2.raw
	env MTOOLSRC=$(MTOOLSRC) mdeltree c:/tmp
	cp $(DISK) mtools-rm-ref-output-2.raw
	env DISK="mtools-rm-output-2.raw" RM_OUTPUT="mtools-rm-output-2.raw" \
	$(ACL2) -- -r "/tmp" < rm-replicant.lisp

unlink-ref-output-1.raw unlink-output-1.raw: $(MOUNTPOINT) rm-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) unlink-ref-output-1.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos unlink-ref-output-1.raw $(MOUNTPOINT)
	unlink $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RM_OUTPUT="unlink-output-1.raw" \
	$(ACL2) -- "/initrd.img" \
	< rm-replicant.lisp

unlink-ref-output-2.raw unlink-output-2.raw: $(MOUNTPOINT) rm-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt $(MOUNTPOINT)/initrd.img
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt $(MOUNTPOINT)/initrd$$i1.img; \
	done
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) unlink-ref-output-2.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos unlink-ref-output-2.raw $(MOUNTPOINT)
	unlink $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RM_OUTPUT="unlink-output-2.raw" \
	$(ACL2) -- "/initrd.img" \
	< rm-replicant.lisp

unlink-ref-output-3.raw unlink-output-3.raw: $(MOUNTPOINT) rm-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt $(MOUNTPOINT)/initrd.img
	mkdir $(MOUNTPOINT)/tmp
	cp input-1204-bytes.txt $(MOUNTPOINT)/tmp/file.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) unlink-ref-output-3.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos unlink-ref-output-3.raw $(MOUNTPOINT)
	unlink $(MOUNTPOINT)/tmp/file.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RM_OUTPUT="unlink-output-3.raw" \
	$(ACL2) -- "/tmp/file.txt" \
	< rm-replicant.lisp

mkdir-ref-output-1.raw mkdir-output-1.raw: $(MOUNTPOINT) mkdir-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) mkdir-ref-output-1.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos mkdir-ref-output-1.raw $(MOUNTPOINT)
	mkdir $(MOUNTPOINT)/dir1
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) MKDIR_OUTPUT="mkdir-output-1.raw" \
	$(ACL2) -- "/dir1" < mkdir-replicant.lisp

mkdir-ref-output-2.raw mkdir-output-2.raw: $(MOUNTPOINT) mkdir-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir $(MOUNTPOINT)/dir1
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) mkdir-ref-output-2.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos mkdir-ref-output-2.raw $(MOUNTPOINT)
	mkdir $(MOUNTPOINT)/dir1/dir2
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) MKDIR_OUTPUT="mkdir-output-2.raw" \
	$(ACL2) -- "/dir1/dir2" < mkdir-replicant.lisp

mtools-mkdir-ref-output-1.raw mtools-mkdir-output-1.raw: mkdir-replicant.lisp
	rm -f $(DISK) mtools-mkdir-ref-output-1.raw
	dd if=/dev/zero of=$(DISK) bs=4096 count=17920
	env MTOOLSRC=$(MTOOLSRC) mformat -T 140000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	cp $(DISK) mtools-mkdir-output-1.raw
	env MTOOLSRC=$(MTOOLSRC) mmd c:/tmp
	cp $(DISK) mtools-mkdir-ref-output-1.raw
	env DISK="mtools-mkdir-output-1.raw" MKDIR_OUTPUT="mtools-mkdir-output-1.raw" \
	$(ACL2) -- "/tmp" \
	< mkdir-replicant.lisp

rmdir-ref-output-1.raw rmdir-output-1.raw: $(MOUNTPOINT) rmdir-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	mkdir $(MOUNTPOINT)/dir1
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) rmdir-ref-output-1.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos rmdir-ref-output-1.raw $(MOUNTPOINT)
	rmdir $(MOUNTPOINT)/dir1
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RMDIR_OUTPUT="rmdir-output-1.raw" \
	$(ACL2) -- "/dir1" < rmdir-replicant.lisp

rmdir-ref-output-2.raw rmdir-output-2.raw: $(MOUNTPOINT) rmdir-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir -p $(MOUNTPOINT)/dir1/dir2
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) rmdir-ref-output-2.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos rmdir-ref-output-2.raw $(MOUNTPOINT)
	rmdir $(MOUNTPOINT)/dir1/dir2
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) RMDIR_OUTPUT="rmdir-output-2.raw" \
	$(ACL2) -- "/dir1/dir2" < rmdir-replicant.lisp

mtools-rmdir-ref-output-1.raw mtools-rmdir-output-1.raw: rmdir-replicant.lisp
	rm -f $(DISK) mtools-rmdir-ref-output-1.raw
	dd if=/dev/zero of=$(DISK) bs=4096 count=17920
	env MTOOLSRC=$(MTOOLSRC) mformat -T 140000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	env MTOOLSRC=$(MTOOLSRC) mmd c:/tmp
	cp $(DISK) mtools-rmdir-output-1.raw
	env MTOOLSRC=$(MTOOLSRC) mrd c:/tmp
	cp $(DISK) mtools-rmdir-ref-output-1.raw
	env DISK="mtools-rmdir-output-1.raw" RMDIR_OUTPUT="mtools-rmdir-output-1.raw" \
	$(ACL2) -- "/tmp" \
	< rmdir-replicant.lisp

mv-ref-output-1.raw mv-output-1.raw: $(MOUNTPOINT) mv-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt $(MOUNTPOINT)/initrd.img
	mkdir $(MOUNTPOINT)/tmp
	cp input-1204-bytes.txt $(MOUNTPOINT)/tmp/file1.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) mv-ref-output-1.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos mv-ref-output-1.raw $(MOUNTPOINT)
	mv $(MOUNTPOINT)/tmp/file1.txt $(MOUNTPOINT)/tmp/file2.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) MV_OUTPUT="mv-output-1.raw" \
	$(ACL2) -- "/tmp/file1.txt" "/tmp/file2.txt" \
	< mv-replicant.lisp

mtools-mv-ref-output-1.raw mtools-mv-output-1.raw: mv-replicant.lisp
	rm -f $(DISK) mtools-mv-ref-output-1.raw
	dd if=/dev/zero of=$(DISK) bs=4096 count=17920
	env MTOOLSRC=$(MTOOLSRC) mformat -T 140000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	env MTOOLSRC=$(MTOOLSRC) mmd c:/tmp
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/tmp/file1.txt
	cp $(DISK) mtools-mv-output-1.raw
	env MTOOLSRC=$(MTOOLSRC) mmove c:/tmp/file1.txt c:/tmp/file2.txt
	cp $(DISK) mtools-mv-ref-output-1.raw
	env DISK="mtools-mv-output-1.raw" MV_OUTPUT="mtools-mv-output-1.raw" \
	$(ACL2) -- "/tmp/file1.txt" "/tmp/file2.txt" < mv-replicant.lisp

mtools-mv-ref-output-2.raw mtools-mv-output-2.raw: mv-replicant.lisp
	rm -f $(DISK) mtools-mv-ref-output-2.raw
	dd if=/dev/zero of=$(DISK) bs=4096 count=17920
	env MTOOLSRC=$(MTOOLSRC) mformat -T 140000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	env MTOOLSRC=$(MTOOLSRC) mmd c:/tmp
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/tmp/file1.txt
	cp $(DISK) mtools-mv-output-2.raw
	env MTOOLSRC=$(MTOOLSRC) mren c:/tmp/file1.txt c:/tmp/file2.txt
	cp $(DISK) mtools-mv-ref-output-2.raw
	env DISK="mtools-mv-output-2.raw" MV_OUTPUT="mtools-mv-output-2.raw" \
	$(ACL2) -- "/tmp/file1.txt" "/tmp/file2.txt" < mv-replicant.lisp

ls-ref-output-1.txt ls-output-1.txt: $(MOUNTPOINT) ls-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	ls -1d $(MOUNTPOINT)/initrd.img > ls-ref-output-1.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) LS_PREFIX=$(MOUNTPOINT) \
	LS_OUTPUT="ls-output-1.txt" $(ACL2) -- -d "/initrd.img" \
	< ls-replicant.lisp

truncate-ref-output-1.raw truncate-output-1.raw: $(MOUNTPOINT) truncate-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) truncate-ref-output-1.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos truncate-ref-output-1.raw $(MOUNTPOINT)
	truncate --size 4626 $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) TRUNCATE_OUTPUT="truncate-output-1.raw" \
	$(ACL2) -- --size 4626 "/initrd.img" \
	< truncate-replicant.lisp

truncate-ref-output-2.raw truncate-output-2.raw: $(MOUNTPOINT) truncate-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-4623-bytes.txt $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	cp $(DISK) truncate-ref-output-2.raw
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos truncate-ref-output-2.raw $(MOUNTPOINT)
	truncate --size 4620 $(MOUNTPOINT)/initrd.img
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) TRUNCATE_OUTPUT="truncate-output-2.raw" \
	$(ACL2) -- --size 4620 "/initrd.img" \
	< truncate-replicant.lisp

debug-do-nothing: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	sleep 1
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir $(MOUNTPOINT)/tmp
	sleep 1
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-and-file: $(MOUNTPOINT)
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir $(MOUNTPOINT)/tmp
	touch $(MOUNTPOINT)/tmp/ticket1.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-copy-file: $(MOUNTPOINT)
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir $(MOUNTPOINT)/tmp
	touch $(MOUNTPOINT)/tmp/ticket1.txt
	cp $(MOUNTPOINT)/tmp/ticket1.txt $(MOUNTPOINT)/tmp/ticket2.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-and-file-rm: $(MOUNTPOINT)
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir $(MOUNTPOINT)/tmp
	touch $(MOUNTPOINT)/tmp/ticket1.txt
	sync $(MOUNTPOINT)/tmp/ticket1.txt
	rm $(MOUNTPOINT)/tmp/ticket1.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-and-file-mv: $(MOUNTPOINT)
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir $(MOUNTPOINT)/tmp
	touch $(MOUNTPOINT)/tmp/ticket1.txt
	sync $(MOUNTPOINT)/tmp/ticket1.txt
	mv $(MOUNTPOINT)/tmp/ticket1.txt $(MOUNTPOINT)/tmp/ticket2.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	true

create-tar-1: $(MOUNTPOINT)
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir -p $(MOUNTPOINT)/tmp/tickets1
	cp input-4623-bytes.txt $(MOUNTPOINT)/tmp/tickets1/ticket1.txt
	cp input-4623-bytes.txt $(MOUNTPOINT)/tmp/tickets1/ticket2.txt
	cd $(MOUNTPOINT)/tmp; tar --create --file tickets1.tar \
	--verbose tickets1
	mv $(MOUNTPOINT)/tmp/tickets1 $(MOUNTPOINT)/tmp/tickets2
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=disk1.raw TAR_INPUT="/tmp/tickets1.tar" \
	TAR_OUTPUT="/tmp" saved_acl2 < tar-reader.lisp
	true

# The following test creates a 128 MB disk image, copies a file to the
# root directory, reads it in ACL2, then writes it back without change.
mtools-read-write-test-128MB: read-disk-image-write-disk-image.lisp
	rm -f $(DISK)
	dd if=/dev/zero of=$(DISK) bs=4096 count=32768
	env MTOOLSRC=$(MTOOLSRC) mformat -T 256000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	env DISK=$(DISK) $(ACL2) -- < read-disk-image-write-disk-image.lisp

# The following test creates a 256 MB disk image, copies a file to the
# root directory, reads it in ACL2, then writes it back without change.
mtools-read-write-test-256MB: read-disk-image-write-disk-image.lisp
	rm -f $(DISK)
	dd if=/dev/zero of=$(DISK) bs=4096 count=65536
	env MTOOLSRC=$(MTOOLSRC) mformat -T 512000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	env DISK=$(DISK) $(ACL2) -- < read-disk-image-write-disk-image.lisp

# The following test creates a 512 MB disk image, copies a file to the
# root directory, reads it in ACL2, then writes it back without change.
mtools-read-write-test-512MB: read-disk-image-write-disk-image.lisp
	rm -f $(DISK)
	dd if=/dev/zero of=$(DISK) bs=4096 count=131072
	env MTOOLSRC=$(MTOOLSRC) mformat -T 1024000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	env DISK=$(DISK) $(ACL2) -- < read-disk-image-write-disk-image.lisp

# The following test creates a 1024 MB disk image, copies a file to the
# root directory, reads it in ACL2, then writes it back without change.
mtools-read-write-test-1024MB: read-disk-image-write-disk-image.lisp
	rm -f $(DISK)
	dd if=/dev/zero of=$(DISK) bs=4096 count=262144
	env MTOOLSRC=$(MTOOLSRC) mformat -T 2048000 -h 64 -s 32 -S \
	2 -F -c 2 c:
	env MTOOLSRC=$(MTOOLSRC) mcopy input-1204-bytes.txt c:/vmlinuz
	env DISK=$(DISK) $(ACL2) -- < read-disk-image-write-disk-image.lisp
