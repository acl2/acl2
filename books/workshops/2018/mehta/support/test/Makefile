test: test-cp-replicant-1 test-cp-replicant-2 test-cp-replicant-3 \
test-cp-replicant-4 test-mkfs-replicant-1 test-mkfs-replicant-2 \
test-mkfs-replicant-3

.PHONY: clean-mountpoint test test-cp-replicant-1 \
test-cp-replicant-2 test-cp-replicant-3 test-cp-replicant-4 \
test-mkfs-replicant-1 test-mkfs-replicant-2 test-mkfs-replicant-3

.PHONY: debug-create-dir-and-file debug-create-dir debug-do-nothing \
debug-create-dir-copy-file

DISK=disk1.raw
SIZE=70000
MOUNTPOINT=mount1
UID=$(shell id -u)
GID=$(shell id -g)

clean-mountpoint:
	rm -rf $(MOUNTPOINT)

clean-fusepoint:
	rm -rf  $(MOUNTPOINT)

$(MOUNTPOINT):
	rm -rf $(MOUNTPOINT)
	mkdir -p $(MOUNTPOINT)

test-cp-replicant-1: cp-ref-output-1.txt cp-output-1.txt
	diff -u -i cp-ref-output-1.txt cp-output-1.txt

test-cp-replicant-2: cp-ref-output-2.txt cp-output-2.txt
	diff -u -i cp-ref-output-2.txt cp-output-2.txt

test-cp-replicant-3: cp-ref-output-3.txt cp-output-3.txt
	diff -u -i cp-ref-output-3.txt cp-output-3.txt

test-cp-replicant-4: cp-ref-output-4.txt cp-output-4.txt
	diff -u -i cp-ref-output-4.txt cp-output-4.txt

test-cp-replicant-5: cp-ref-output-5.txt cp-output-5.txt
	diff -u -i cp-ref-output-5.txt cp-output-5.txt

test-mkfs-replicant-1: mkfs-ref-output-1.txt mkfs-output-1.txt
	diff -u -i mkfs-ref-output-1.txt mkfs-output-1.txt

test-mkfs-replicant-2: mkfs-ref-output-2.txt mkfs-output-2.txt
	diff -u -i mkfs-ref-output-2.txt mkfs-output-2.txt

test-mkfs-replicant-3: mkfs-ref-output-3.txt mkfs-output-3.txt
	diff -u -i mkfs-ref-output-3.txt mkfs-output-3.txt

cp-ref-output-1.txt cp-output-1.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	echo "four" >  $(MOUNTPOINT)/vmlinuz
	cat  $(MOUNTPOINT)/vmlinuz > cp-ref-output-1.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-1.txt" \
	CP_INPUT="VMLINUZ    " $(ACL2) < cp-replicant.lisp

cp-ref-output-2.txt cp-output-2.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt  $(MOUNTPOINT)/vmlinuz
	cat  $(MOUNTPOINT)/vmlinuz > cp-ref-output-2.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-2.txt" \
	CP_INPUT="VMLINUZ    " $(ACL2) < cp-replicant.lisp

cp-ref-output-3.txt cp-output-3.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt  $(MOUNTPOINT)/vmlinuz
	cp input-4623-bytes.txt  $(MOUNTPOINT)/initrd.img
	cat  $(MOUNTPOINT)/initrd.img > cp-ref-output-3.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-3.txt" \
	CP_INPUT="INITRD  IMG" $(ACL2) < cp-replicant.lisp

cp-ref-output-4.txt cp-output-4.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt  $(MOUNTPOINT)/initrd$$i1.img; \
	done
	cp input-4623-bytes.txt  $(MOUNTPOINT)/initrd.img
	cat  $(MOUNTPOINT)/initrd.img > cp-ref-output-4.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-4.txt" \
	CP_INPUT="INITRD  IMG" $(ACL2) < cp-replicant.lisp

cp-ref-output-5.txt cp-output-5.txt: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	cp input-1204-bytes.txt  $(MOUNTPOINT)/initrd.img
	sync  $(MOUNTPOINT)/initrd.img
	rm  $(MOUNTPOINT)/initrd.img
	for i1 in $(shell seq 1 32); do \
		cp input-1204-bytes.txt  $(MOUNTPOINT)/initrd$$i1.img; \
	done
	cp input-4623-bytes.txt  $(MOUNTPOINT)/initrd.img
	cat  $(MOUNTPOINT)/initrd.img > cp-ref-output-5.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	env DISK=$(DISK) CP_OUTPUT="cp-output-5.txt" \
	CP_INPUT="INITRD  IMG" $(ACL2) < cp-replicant.lisp

mkfs-ref-output-1.txt mkfs-output-1.txt: $(MOUNTPOINT) \
mkfs.fat-3.0.28-replicant.lisp
	rm -f $(DISK)
	(mkfs.fat -C -v -F 32 -s 1 $(DISK) $(SIZE)) > mkfs-ref-output-1.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-1.txt" $(ACL2) < \
	mkfs.fat-3.0.28-replicant.lisp

mkfs-ref-output-2.txt mkfs-output-2.txt: $(MOUNTPOINT) \
mkfs.fat-3.0.28-replicant.lisp
	rm -f $(DISK)
	(mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)) > mkfs-ref-output-2.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-2.txt" $(ACL2) < \
	mkfs.fat-3.0.28-replicant.lisp

# this case does not actually produce a valid FAT32 filesystem, since
# there are fewer than 65525 clusters.
mkfs-ref-output-3.txt mkfs-output-3.txt: $(MOUNTPOINT) \
mkfs.fat-3.0.28-replicant.lisp
	rm -f $(DISK)
	(mkfs.fat -C -v -F 32 -s 4 $(DISK) $(SIZE)) > mkfs-ref-output-3.txt
	env DISK=$(DISK) MKFS_OUTPUT="mkfs-output-3.txt" $(ACL2) < \
	mkfs.fat-3.0.28-replicant.lisp

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
	mkdir  $(MOUNTPOINT)/tmp
	sleep 1
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-and-file: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir  $(MOUNTPOINT)/tmp
	touch  $(MOUNTPOINT)/tmp/ticket1.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	true

debug-create-dir-copy-file: $(MOUNTPOINT) cp-replicant.lisp
	rm -f $(DISK)
	mkfs.fat -C -v -F 32 -s 2 $(DISK) $(SIZE)
	sudo mount -o loop,uid=$(UID),gid=$(GID) -t msdos $(DISK) $(MOUNTPOINT)
	mkdir  $(MOUNTPOINT)/tmp
	touch  $(MOUNTPOINT)/tmp/ticket1.txt
	cp  $(MOUNTPOINT)/tmp/ticket1.txt  $(MOUNTPOINT)/tmp/ticket2.txt
	sleep 1
	sudo umount $(MOUNTPOINT)
	true
