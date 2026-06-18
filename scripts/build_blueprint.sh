set -x -e

cd verso_blueprint
lake exe cache get
lake build
lake exe blueprint-gen --output _out/site
mkdir -p _out/site/html-multi/static
cp static_files/* _out/site/html-multi/static
cd ..

# Copy outputs to home_page
mkdir -p home_page/verso_blueprint
cp -r verso_blueprint/_out/site/html-multi/* home_page/verso_blueprint
