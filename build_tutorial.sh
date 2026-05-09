set -x -e

# Build tutorial
cd tutorial
lake build
lake exe manual --output _out/site
mkdir -p _out/site/html-multi/static
cp static_files/* _out/site/html-multi/static
cd ..

# Copy outputs to home_page
mkdir -p home_page/tutorial
cp -r tutorial/_out/site/html-multi/* home_page/tutorial
