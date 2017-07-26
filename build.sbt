enablePlugins(ScalaJSPlugin, WorkbenchPlugin)

//lazy val js = (project in file("js")).enablePlugins(ScalaJSPlugin)
//scalaVersion in js := "2.12.1" // Or the right version
//addCommandAlias("runWithJS", ";fastOptJS;run")

name := "parameterised-connectors"

version := "1.0"

scalaVersion := "2.11.8" // "2.12.1"
  //"2.10.5" //"2.11.7" -> strangely requires old version of picc (github)


// more warnings
scalacOptions ++= Seq("-unchecked", "-deprecation","-feature")

// more complete check for complete "cases" (scala 2.10)
// initialize ~= { _ => sys.props("scalac.patmat.analysisBudget") = "512" }


libraryDependencies ++= Seq(
  "junit" % "junit" % "4.12",
  "org.choco-solver" % "choco-solver" % "3.3.1-j7",
  "org.slf4j" % "slf4j-simple" % "1.7.12",
  "io.github.nicolasstucki" %% "multisets" % "0.3",
  "org.scala-lang" % "scala-compiler" % scalaVersion.value,
  // "org.scala-js" %% "scalajs-dom" % "0.9.1",
  // "com.lihaoyi" %% "utest" % "0.4.5" % "test"
  "org.scala-js" %%% "scalajs-dom" % "0.9.1",
  "com.lihaoyi" %%% "scalatags" % "0.6.1",
  "org.scala-lang.modules" %%% "scala-parser-combinators" % "1.0.5",
  "org.singlespaced" %%% "scalajs-d3" % "0.3.4"
//   "org.scala-lang" % "scala-reflect" % scalaVersion.value,
)


// libraryDependencies += ProjectRef(uri("https://github.com/joseproenca/picc"),"picc")

//libraryDependencies += "org.matheclipse" % "matheclipse-parser" % "0.0.7"
//
//resolvers += "org-matheclipse-repository" at "http://symja.googlecode.com/svn/maven-repository/"


//libraryDependencies += "cc.redberry" % "core" % "1.1.8"

//libraryDependencies += "org.apache.logging.log4j" % "log4j-core" % "2.3"

//libraryDependencies += "org.apache.logging.log4j" %% "log4j-core" % "2.3"

//libraryDependencies += "org.apache.logging.log4j" %% "log4j-api" % "2.3"


