set -x -e

lake build

# Build tutorial
lake exe tutorial --output LMLTutorial/_out/site
mkdir -p LMLTutorial/_out/site/html-multi/static
cp LMLTutorial/static_files/* LMLTutorial/_out/site/html-multi/static

# Build docs
lake exe docs --output LMLDocs/_out/site
mkdir -p LMLDocs/_out/site/html-multi/static
cp LMLDocs/static_files/* LMLDocs/_out/site/html-multi/static

# Copy outputs to home_page
mkdir -p home_page/tutorial
cp -r LMLTutorial/_out/site/html-multi/* home_page/tutorial
mkdir -p home_page/defdocs
cp -r LMLDocs/_out/site/html-multi/* home_page/defdocs
