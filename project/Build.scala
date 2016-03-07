import sbt._

object MyBuild extends Build {
  lazy val root = Project("root", file(".")) dependsOn(piccProject)
  lazy val piccProject = RootProject(uri("git://github.com/joseproenca/picc.git"))
}