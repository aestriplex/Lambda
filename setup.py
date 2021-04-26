import setuptools

with open("README.md", "r", encoding="utf-8") as f :
    long_description = f.read()

setuptools.setup(
    name="lmb",
    version="0.1.0",
    author="Matteo Nicoli",
    author_email="aestriplex@post.com",
    description="nothing but master",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/aestriplex/Lambda",
    project_urls={
        "Bug Tracker": "https://github.com/aestriplex/Lambda/issues",
    },
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: Unix-like",
    ],
    install_requires=[
        "esprima",
        "z3-prover",
        "jsbeautifier"
    ],
    package_dir={"": "src/"},
    packages = ["lmb",
                "lmb.parser",
                "lmb.parser.javascript",
                "lmb.parser.javascript.std_obj"],
    python_requires=">=3.7.3",
)