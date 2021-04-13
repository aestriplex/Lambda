import setuptools

with open("README.md", "r", encoding="utf-8") as f :
    long_description = f.read()

setuptools.setup(
    name="Lambda-lmb",
    version="0.0.2",
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
    package_dir={"": "src/lmb"},
    packages=setuptools.find_packages(where="src/lmb"),
    python_requires=">=3.7.3",
)