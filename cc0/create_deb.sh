#!/bin/bash -xe

# Make sure we are running on Linux
if [[ `uname` != Linux ]]; then 
    echo "This script is only for Linux"
    exit 1
fi 

VERSION=`./get_version.sh`
ROOT=`pwd`

# Create working directory
WORKING_DIR=cc0_${VERSION}_debian

if [[ -e $WORKING_DIR ]]; then 
    echo "Temp directory $WORKING_DIR already exists"
    echo "This probably happened if this script failed"
    echo "Delete it and re-run the script"
    exit 1
fi

# Make sure we are up to date
if ! make -j -s --no-print-directory 2> /dev/null ; then
    echo "Make failed! Fix compilation problems and rerun this script"
fi 

mkdir $WORKING_DIR
pushd $WORKING_DIR

# Create manifest file, DEBIAN/control
mkdir DEBIAN 
pushd DEBIAN

cat << EOF > control
Package: cc0
Version: $VERSION
Section: base
Priority: optional
Architecture: amd64
Depends: build-essential (>= 12.6), libgmp10 (>= 2:6.1.2), libpng16-16 (>= 1.6.36-6)
Maintainer: Ishan Bhargava <ibhargav@andrew.cmu.edu>
Description: C0 compiler and interpreter
EOF

popd

# Install files to /usr/share/cc0.
# This is necessary since CC0 relies on runtime/lib directories being
# in the parent directory of bin/cc0 etc
mkdir -p usr/share/cc0
pushd usr/share/cc0

cp $ROOT/README_CC0.txt .
cp -r $ROOT/bin .
cp -r $ROOT/include/ .
cp -r $ROOT/lib .
cp -r $ROOT/runtime .

popd

# Install wrapper scripts in /usr/bin
mkdir -p usr/bin 
pushd usr/bin

cat << EOF > cc0
/usr/share/cc0/bin/cc0 \$*
EOF

cat << EOF > coin
/usr/share/cc0/bin/coin \$*
EOF

chmod +x cc0 coin

popd

# Now we can create the package
popd
dpkg-deb --build --root-owner-group $WORKING_DIR 

# Remove working directory
rm -rf $WORKING_DIR