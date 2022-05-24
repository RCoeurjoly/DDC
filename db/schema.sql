/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!40101 SET NAMES utf8mb4 */;
/*!40103 SET @OLD_TIME_ZONE=@@TIME_ZONE */;
/*!40103 SET TIME_ZONE='+00:00' */;
/*!40014 SET @OLD_UNIQUE_CHECKS=@@UNIQUE_CHECKS, UNIQUE_CHECKS=0 */;
/*!40014 SET @OLD_FOREIGN_KEY_CHECKS=@@FOREIGN_KEY_CHECKS, FOREIGN_KEY_CHECKS=0 */;
/*!40101 SET @OLD_SQL_MODE=@@SQL_MODE, SQL_MODE='NO_AUTO_VALUE_ON_ZERO' */;
/*!40111 SET @OLD_SQL_NOTES=@@SQL_NOTES, SQL_NOTES=0 */;

--
-- Table structure for table `arguments_on_entry`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `arguments_on_entry` (
  `node_id` int(10) unsigned DEFAULT NULL,
  `argument_name` char(255) NOT NULL DEFAULT '',
  `argument_value` blob NOT NULL,
  UNIQUE KEY `node_id` (`node_id`,`argument_name`),
  CONSTRAINT `arguments_on_entry_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`node_id`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `arguments_when_returning`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `arguments_when_returning` (
  `node_id` int(10) unsigned DEFAULT NULL,
  `argument_name` char(255) NOT NULL DEFAULT '',
  `argument_value` blob NOT NULL,
  UNIQUE KEY `node_id` (`node_id`,`argument_name`),
  CONSTRAINT `arguments_when_returning_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`node_id`),
  CONSTRAINT `arguments_when_returning_fk_2` FOREIGN KEY (`node_id`, `argument_name`) REFERENCES `arguments_on_entry` (`node_id`, `argument_name`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `global_variables_on_entry`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `global_variables_on_entry` (
  `node_id` int(10) unsigned DEFAULT NULL,
  `global_variable_name` char(255) NOT NULL DEFAULT '',
  `global_variable_value` blob NOT NULL,
  UNIQUE KEY `node_id` (`node_id`,`global_variable_name`),
  CONSTRAINT `global_variables_on_entry_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`node_id`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `global_variables_when_returning`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `global_variables_when_returning` (
  `node_id` int(10) unsigned DEFAULT NULL,
  `global_variable_name` char(255) NOT NULL DEFAULT '',
  `global_variable_value` blob NOT NULL,
  UNIQUE KEY `node_id` (`node_id`,`global_variable_name`),
  CONSTRAINT `global_variables_when_returning_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`node_id`),
  CONSTRAINT `global_variables_when_returning_fk_2` FOREIGN KEY (`node_id`, `global_variable_name`) REFERENCES `global_variables_on_entry` (`node_id`, `global_variable_name`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `nodes`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `nodes` (
  `node_id` int(10) unsigned DEFAULT NULL,
  `parent_node_id` int(10) unsigned DEFAULT NULL,
  `birth_order` int(10) unsigned DEFAULT NULL,
  `function_name` blob NOT NULL,
  `return_value` blob NOT NULL,
  `object_on_entry` blob NOT NULL,
  `object_when_returning` blob NOT NULL,
  `creation_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `finishing_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00' ON UPDATE CURRENT_TIMESTAMP,
  `finished` tinyint(1) NOT NULL DEFAULT '0',
  UNIQUE KEY `node_id` (`node_id`),
  UNIQUE KEY `parent_node_id` (`parent_node_id`,`birth_order`),
  CONSTRAINT `parent_node_exists` FOREIGN KEY (`parent_node_id`) REFERENCES `nodes` (`node_id`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `schema_migrations`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `schema_migrations` (
  `version` varchar(255) COLLATE latin1_bin NOT NULL,
  PRIMARY KEY (`version`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1 COLLATE=latin1_bin;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping routines for database 'nodes'
--
/*!40103 SET TIME_ZONE=@OLD_TIME_ZONE */;

/*!40101 SET SQL_MODE=@OLD_SQL_MODE */;
/*!40014 SET FOREIGN_KEY_CHECKS=@OLD_FOREIGN_KEY_CHECKS */;
/*!40014 SET UNIQUE_CHECKS=@OLD_UNIQUE_CHECKS */;
/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
/*!40111 SET SQL_NOTES=@OLD_SQL_NOTES */;

-- Dump completed

--
-- Dbmate schema migrations
--

LOCK TABLES `schema_migrations` WRITE;
INSERT INTO `schema_migrations` (version) VALUES
  ('20220522161939'),
  ('20220523165858'),
  ('20220523165910'),
  ('20220523165927'),
  ('20220523165938');
UNLOCK TABLES;
